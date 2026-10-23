//! Scalar binary64 port of FilterPy's GHFilter constructor and update method.
//! Source: FilterPy gh_filter.py at 3b51149, copyright 2015 Roger R. Labbe Jr.
//! MIT source license; see the accompanying LICENSE-FilterPy.
//! Arithmetic order follows that source.
//! Arrays, subclass dispatch and physical tracking accuracy are outside this port.

#[derive(Clone, Copy, Debug)]
pub struct GhFilter {
    pub x: f64,
    pub dx: f64,
    pub dt: f64,
    pub g: f64,
    pub h: f64,
    pub dx_prediction: f64,
    pub x_prediction: f64,
    pub y: f64,
    pub z: f64,
}

impl GhFilter {
    pub fn new(x: f64, dx: f64, dt: f64, g: f64, h: f64) -> Self {
        Self {
            x,
            dx,
            dt,
            g,
            h,
            dx_prediction: dx,
            x_prediction: x,
            y: 0.0,
            z: 0.0,
        }
    }

    /// Updates state; omitted gains use the stored values without changing them.
    /// As in the original update method, the public `z` field is left unchanged.
    pub fn update(&mut self, z: f64, g: Option<f64>, h: Option<f64>) -> (f64, f64) {
        let g = match g {
            Some(value) => value,
            None => self.g,
        };
        let h = match h {
            Some(value) => value,
            None => self.h,
        };
        self.dx_prediction = self.dx;
        self.x_prediction = self.x + (self.dx * self.dt);
        self.y = z - self.x_prediction;
        self.dx = self.dx_prediction + h * self.y / self.dt;
        self.x = self.x_prediction + g * self.y;
        (self.x, self.dx)
    }
}
