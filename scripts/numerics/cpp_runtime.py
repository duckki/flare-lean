"""Compile and execute the original selected C++ header, retaining its tool identity."""
import re
import sys


def source_results(program,source,cases,runtime,output,work,runner):
    from .workflow import save
    root=output/'source-diagnostics';root.mkdir(exist_ok=True)
    original=root/'original.hpp';original.write_text(source)
    input_file=root/'inputs.hex'
    input_file.write_text('\n'.join(' '.join(f'{x:016x}' for x in case) for case in cases)+'\n')
    checks=[]
    for name,bits in program.selection['constants'].items():
        checks += [f'static_assert(std::is_same_v<decltype(({name})), double>);',
                   f'static_assert(std::bit_cast<std::uint64_t>({name}) == {bits}ULL);']
    arguments=', '.join(f'std::bit_cast<double>(w[{i}])' for i in range(len(program.inputs)))
    driver=root/'driver.cpp'
    driver.write_text('\n'.join(['#include <bit>','#include <cstdint>','#include <cfenv>','#include <iostream>',
        '#include <sstream>','#include <string>','#include <type_traits>','#include <limits>',
        '#include "original.hpp"',
        'static_assert(sizeof(double)==8 && std::numeric_limits<double>::is_iec559);',*checks,
        'int main() { if (std::fegetround()!=FE_TONEAREST) return 3; std::string line;',
        'while (std::getline(std::cin,line)) { std::istringstream in(line);',
        f'std::uint64_t w[{len(program.inputs)}]; for (auto &v:w) in >> std::hex >> v;',
        f'const double out={program.function}({arguments});',
        'std::cout << std::hex << std::bit_cast<std::uint64_t>(out) << "\\n"; } }','']))
    flags=['-std=c++20','-ffp-contract=off','-fno-fast-math']
    if runtime.get('sdk'):flags+=['-isysroot',runtime['sdk']]
    actual=None
    for mode,optimization in [('debug','-O0'),('optimized','-O2')]:
        binary=work/('cpp-'+mode)
        runner.run('source-compile-'+mode,[runtime['executable'],*flags,optimization,driver,'-o',binary],
                   cwd=work,phase='diagnostic',inherit_developer_dir=True)
        wrapper=work/('execute-'+mode+'.py')
        wrapper.write_text('import subprocess\nfrom pathlib import Path\np=subprocess.run('+repr([str(binary)])+
            ',input=Path('+repr(str(input_file))+').read_bytes(),capture_output=True,check=True)\nprint(p.stdout.decode(),end="")\n')
        text=runner.run('source-execute-'+mode,[sys.executable,wrapper],cwd=work,phase='diagnostic')
        rows=text.splitlines()
        if len(rows)!=len(cases) or any(not re.fullmatch('[0-9a-f]{1,16}',r) for r in rows):
            raise ValueError('C++ source returned malformed witness words')
        values=[(int(row,16),) for row in rows]
        if actual is not None and actual!=values:raise ValueError('C++ debug/optimized source results disagree')
        actual=values
    save(output/'cpp-runtime.json',{'standard':'c++20','flags':flags,'modes':['-O0','-O2'],
         'constants':program.selection['constants'],'case_count':len(cases),
         'qualification':'Original header execution and compiler static_assert diagnostics. Source parsing, compiler and hardware fidelity remain trusted; these are not universal source-equivalence proofs.'})
    return actual
