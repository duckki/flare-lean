use crate::gh::GhFilter;
use crate::tracker::*;
#[test]
fn complete_api_defaults_and_overrides_preserve_stored_fields() {
    let mut state = GhFilter::new(1.0, -0.0, 0.125, 0.5, 0.125);
    assert_eq!(state.dx_prediction.to_bits(), (-0.0f64).to_bits());
    assert_eq!(state.x_prediction, 1.0);
    assert_eq!(state.y.to_bits(), 0);
    assert_eq!(state.z.to_bits(), 0);
    state.z = -3.0;
    state.update(2.0, Some(0.25), Some(0.0));
    assert_eq!(state.x, 1.25);
    assert_eq!(state.dx, 0.0);
    assert_eq!((state.g, state.h, state.z), (0.5, 0.125, -3.0));
    assert_eq!(state.y, 1.0);
}
#[test]
fn four_states_and_decisions() {
    let xs = [Measurement { x: 1.0, y: -1.0 }; 8];
    let result = assess(0.0, 0.0, 0.0, 0.0, &xs, 20.0).unwrap();
    assert_eq!(result.decision, Decision::Below);
    let above = assess(0.0, 0.0, 0.0, 0.0, &xs, -20.0).unwrap();
    assert_eq!(above.decision, Decision::Above);
    assert_eq!(assess(0.0, 0.0, 0.0, 0.0, &xs, result.state.horizontal.x).unwrap().decision,
               Decision::Uncertain);
    assert_eq!(result.state.horizontal.x, -result.state.vertical.x);
    assert_eq!(result.state.horizontal.dx, -result.state.vertical.dx);
}
#[test]
fn validation_order_and_no_mutation_on_error() {
    let valid = [Measurement { x: 0.0, y: 0.0 }; 8];
    assert_eq!(assess(f64::NAN, 0.0, 0.0, 0.0, &[], f64::NAN).unwrap_err(), Error::WrongSize);
    assert_eq!(assess(f64::NAN, 0.0, 0.0, 0.0, &valid, f64::NAN).unwrap_err(), Error::InvalidThreshold);
    assert_eq!(assess(f64::NAN, 0.0, 0.0, 0.0, &valid, 0.0).unwrap_err(), Error::InvalidInitial);
    let mut state = PlanarTracker::new(1.0, 0.0, -1.0, 0.0).unwrap();
    assert_eq!(state.update(Measurement { x: 0.0, y: f64::INFINITY }, None, None),
               Err(Error::InvalidMeasurement));
    assert_eq!((state.horizontal.x, state.vertical.x), (1.0, -1.0));
}
#[test]
fn strict_padding_endpoints_are_uncertain() {
    assert_eq!(classify(DECISION_PADDING, 0.0), Decision::Uncertain);
    assert_eq!(classify(-DECISION_PADDING, 0.0), Decision::Uncertain);
    let outside = f64::from_bits(DECISION_PADDING.to_bits() + 1);
    assert_eq!(classify(outside, 0.0), Decision::Above);
    assert_eq!(classify(-outside, 0.0), Decision::Below);
}
