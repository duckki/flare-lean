static double correction(double gain, double residual) {
    return gain * residual;
}

double mean_update(double prior, double gain, double residual) {
    return prior + correction(gain, residual);
}

/*@ requires \valid(state + (0..1));
    requires \valid_read(observation + (0..1));
    requires \separated(state + (0..1), observation + (0..1));
    assigns state[0..1];
*/
void blend(double state[restrict static 2],
           const double observation[restrict static 2], double gain) {
    /*@ loop invariant 0 <= i <= 2;
        loop assigns i, state[0..1];
        loop variant 2-i;
    */
    for (unsigned int i = 0; i < 2; ++i) {
        state[i] = state[i] + gain * (observation[i] - state[i]);
    }
}

struct Calibration {
    double gain;
    double offset;
};

double calibrate(double value, struct Calibration config) {
    return value * config.gain + config.offset;
}

/* Read-only regions may overlap: this function never modifies either input. */
double dot2(const double values[static 2], const double weights[static 2]) {
    double result = 0.0;
    for (unsigned int i = 0; i < 2; ++i) {
        result = result + values[i] * weights[i];
    }
    return result;
}
