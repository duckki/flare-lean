def predict(position: float, velocity: float, acceleration: float, dt: float):
    """One IMU motion kernel; dt is an original Float input, not an integer epoch."""
    squared = dt * dt
    accelerated = squared * acceleration
    half_acceleration = accelerated / 2.0
    translated = position + dt * velocity
    next_position = translated + half_acceleration
    next_velocity = velocity + dt * acceleration
    return next_position, next_velocity
