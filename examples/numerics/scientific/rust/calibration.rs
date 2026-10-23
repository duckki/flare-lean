fn affine(value: f64, gain: f64, offset: f64) -> f64 {
    value * gain + offset
}

pub fn calibrate(values: [f64; 2], gains: [f64; 2], offsets: [f64; 2]) -> [f64; 2] {
    let mut output = [0.0; 2];
    let mut i = 0;
    while i < values.len() {
        output[i] = affine(values[i], gains[i], offsets[i]);
        i += 1;
    }
    output
}
