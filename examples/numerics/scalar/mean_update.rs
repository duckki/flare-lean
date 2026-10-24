pub fn update(x: f64, z: f64, k: f64) -> f64 {
    let r = z - x;
    let m = r * k;
    let a = m + 0.0;
    a + x
}
