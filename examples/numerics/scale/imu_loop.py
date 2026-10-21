def predict(position: float, velocity: float, acceleration: float, dt: float):
    """One IMU motion kernel; dt is an original Float input, not an integer epoch."""
    squared = dt * dt
    accelerated = squared * acceleration
    half_acceleration = accelerated / 2.0
    translated = position + dt * velocity
    next_position = translated + half_acceleration
    next_velocity = velocity + dt * acceleration
    return next_position, next_velocity

# Fixed-arity scale fixtures: each tuple element is an independent original Float input.

def run_1(
    position: float, velocity: float, dt: float, acceleration_000: float,
):
    """1 ordered imu updates; carry both state components between calls."""
    for acceleration in (
        acceleration_000,
    ):
        position, velocity = predict(position, velocity, acceleration, dt)
    return position, velocity

def run_4(
    position: float, velocity: float, dt: float, acceleration_000: float,
    acceleration_001: float, acceleration_002: float, acceleration_003: float,
):
    """4 ordered imu updates; carry both state components between calls."""
    for acceleration in (
        acceleration_000, acceleration_001, acceleration_002, acceleration_003,
    ):
        position, velocity = predict(position, velocity, acceleration, dt)
    return position, velocity

def run_16(
    position: float, velocity: float, dt: float, acceleration_000: float,
    acceleration_001: float, acceleration_002: float, acceleration_003: float, acceleration_004: float,
    acceleration_005: float, acceleration_006: float, acceleration_007: float, acceleration_008: float,
    acceleration_009: float, acceleration_010: float, acceleration_011: float, acceleration_012: float,
    acceleration_013: float, acceleration_014: float, acceleration_015: float,
):
    """16 ordered imu updates; carry both state components between calls."""
    for acceleration in (
        acceleration_000, acceleration_001, acceleration_002, acceleration_003, acceleration_004,
        acceleration_005, acceleration_006, acceleration_007, acceleration_008, acceleration_009,
        acceleration_010, acceleration_011, acceleration_012, acceleration_013, acceleration_014,
        acceleration_015,
    ):
        position, velocity = predict(position, velocity, acceleration, dt)
    return position, velocity

def run_48(
    position: float, velocity: float, dt: float, acceleration_000: float,
    acceleration_001: float, acceleration_002: float, acceleration_003: float, acceleration_004: float,
    acceleration_005: float, acceleration_006: float, acceleration_007: float, acceleration_008: float,
    acceleration_009: float, acceleration_010: float, acceleration_011: float, acceleration_012: float,
    acceleration_013: float, acceleration_014: float, acceleration_015: float, acceleration_016: float,
    acceleration_017: float, acceleration_018: float, acceleration_019: float, acceleration_020: float,
    acceleration_021: float, acceleration_022: float, acceleration_023: float, acceleration_024: float,
    acceleration_025: float, acceleration_026: float, acceleration_027: float, acceleration_028: float,
    acceleration_029: float, acceleration_030: float, acceleration_031: float, acceleration_032: float,
    acceleration_033: float, acceleration_034: float, acceleration_035: float, acceleration_036: float,
    acceleration_037: float, acceleration_038: float, acceleration_039: float, acceleration_040: float,
    acceleration_041: float, acceleration_042: float, acceleration_043: float, acceleration_044: float,
    acceleration_045: float, acceleration_046: float, acceleration_047: float,
):
    """48 ordered imu updates; carry both state components between calls."""
    for acceleration in (
        acceleration_000, acceleration_001, acceleration_002, acceleration_003, acceleration_004,
        acceleration_005, acceleration_006, acceleration_007, acceleration_008, acceleration_009,
        acceleration_010, acceleration_011, acceleration_012, acceleration_013, acceleration_014,
        acceleration_015, acceleration_016, acceleration_017, acceleration_018, acceleration_019,
        acceleration_020, acceleration_021, acceleration_022, acceleration_023, acceleration_024,
        acceleration_025, acceleration_026, acceleration_027, acceleration_028, acceleration_029,
        acceleration_030, acceleration_031, acceleration_032, acceleration_033, acceleration_034,
        acceleration_035, acceleration_036, acceleration_037, acceleration_038, acceleration_039,
        acceleration_040, acceleration_041, acceleration_042, acceleration_043, acceleration_044,
        acceleration_045, acceleration_046, acceleration_047,
    ):
        position, velocity = predict(position, velocity, acceleration, dt)
    return position, velocity
