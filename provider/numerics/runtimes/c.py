"""Compile and diagnose the original C API, including its actual memory effects."""
from pathlib import Path


FLAGS=['-std=c11','-fno-fast-math','-ffp-contract=off','-fexcess-precision=standard','-Werror']


def driver(program):
    lines=['#include <stdio.h>','#include <stdint.h>','#include <inttypes.h>',
        '#include <string.h>','#include <assert.h>','#include <float.h>','#include <limits.h>',
        '#include <fenv.h>','#include "source.c"',
        '_Static_assert(sizeof(double)==8 && FLT_RADIX==2 && DBL_MANT_DIG==53 && DBL_MAX_EXP==1024 && FLT_EVAL_METHOD==0, "binary64 required");',
        '_Static_assert(UINT_MAX==4294967295U, "32-bit unsigned int required");',
        'static double flare_from_word(uint64_t w) { double x; memcpy(&x,&w,8); return x; }',
        'static uint64_t flare_to_word(double x) { uint64_t w; memcpy(&w,&x,8); return w; }',
        'int main(void) {', '  assert(fegetround()==FE_TONEAREST);',
        '  volatile double tiny=flare_from_word(1); assert(tiny*1.0==tiny);',
        '  volatile double one=1.0; assert(one+0x1p-53==one);',
        '  FILE *in=fopen("inputs.hex","r"); assert(in);',
        '  uint64_t w['+str(len(program.inputs))+'];',
        '  while (fscanf(in,"%" SCNx64,&w[0])==1) {']
    for i in range(1,len(program.inputs)):lines.append(f'    assert(fscanf(in,"%" SCNx64,&w[{i}])==1);')
    offset=0;args=[]
    for p in program.c['api']:
        values=['flare_from_word(w['+str(offset+i)+'])' for i in range(len(p['inputs']))]
        name='flare_arg_'+p['name'];args.append(name)
        if p['kind']=='scalar':lines.append('    double '+name+'='+values[0]+';')
        elif p['kind']=='buffer':lines.append('    double '+name+'['+str(p['length'])+']={'+','.join(values)+'};')
        else:lines.append('    struct '+p['tag']+' '+name+'={'+','.join(values)+'};')
        offset+=len(values)
    call=program.function+'('+','.join(args)+')'
    if program.c['return_type']=='double':
        lines.append('    double flare_result='+call+';');outputs=['flare_result']
    else:
        lines.append('    '+call+';')
        outputs=['flare_arg_'+program.c['writable']+'['+str(i)+']' for i in range(len(program.outputs))]
    lines += ['    printf("'+' '.join(['%016" PRIx64 "']*len(outputs))+'\\n",'+
                ','.join('flare_to_word('+v+')' for v in outputs)+');',
              '  }','  assert(feof(in)); assert(fclose(in)==0); return 0;','}']
    return '\n'.join(lines)+'\n'


def source_results(program,source,cases,runtime,output,work,runner):
    from numerics.workflow.certification import save
    root=output/'source-diagnostics'
    (root/'source.c').write_text(source)
    script=root/'driver.c';script.write_text(driver(program))
    rows=[];config=[]
    for label,flags in [('debug',['-O0']),('optimized',['-O2']),
                        ('sanitized',['-O1','-fsanitize=address,undefined','-fno-sanitize-recover=all'])]:
        binary=work/('c-source-'+label)
        platform_flags=['-isysroot',runtime['sdk']] if runtime.get('sdk') else []
        command=[runtime['executable'],*FLAGS,*flags,*platform_flags,script,'-lm','-o',binary]
        runner.run('source-compile-'+label,command,cwd=root,phase='diagnostic',inherit_developer_dir=True)
        environment={'ASAN_OPTIONS':'detect_leaks=0:symbolize=0'} if label=='sanitized' else {}
        text=runner.run('source-execute-'+label,[binary],cwd=root,env=environment,phase='diagnostic',inherit_developer_dir=True)
        words=[tuple(int(v,16) for v in line.split()) for line in text.splitlines()]
        if len(words)!=len(cases) or any(len(v)!=len(program.outputs) for v in words):
            raise ValueError('C runtime returned incomplete results')
        if rows and words!=rows:raise ValueError('Original C word results differ across compiler modes')
        rows=words;config.append({'mode':label,'flags':[*FLAGS,*flags,*platform_flags],'environment':environment})
    save(output/'c-runtime.json',{'schema':'c-source-runtime-v1','compiler':runtime,
        'modes':config,'unsigned_int_bits':32,'double_bits':64,
        'qualification':'Original C source at O0/O2 and under address/undefined-behavior sanitizers. Sampled diagnostics are not a compiler or memory-safety proof.'})
    return rows
