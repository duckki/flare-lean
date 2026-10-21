def step(mean: float, variance: float, measurement: float, process_noise: float, measurement_noise: float):
    """One random-walk prediction and scalar Kalman measurement correction."""
    predicted_variance = variance + process_noise
    innovation_variance = predicted_variance + measurement_noise
    gain = predicted_variance / innovation_variance
    innovation = measurement - mean
    next_mean = mean + gain * innovation
    next_variance = (1.0 - gain) * predicted_variance
    return next_mean, next_variance

# Fixed-arity scale fixtures: each tuple element is an independent original Float input.

def run_1(
    mean: float, variance: float, process_noise: float, measurement_noise: float,
    measurement_000: float,
):
    """1 ordered kalman updates; carry both state components between calls."""
    for measurement in (
        measurement_000,
    ):
        mean, variance = step(mean, variance, measurement, process_noise, measurement_noise)
    return mean, variance

def run_4(
    mean: float, variance: float, process_noise: float, measurement_noise: float,
    measurement_000: float, measurement_001: float, measurement_002: float, measurement_003: float,
):
    """4 ordered kalman updates; carry both state components between calls."""
    for measurement in (
        measurement_000, measurement_001, measurement_002, measurement_003,
    ):
        mean, variance = step(mean, variance, measurement, process_noise, measurement_noise)
    return mean, variance

def run_8(
    mean: float, variance: float, process_noise: float, measurement_noise: float,
    measurement_000: float, measurement_001: float, measurement_002: float, measurement_003: float,
    measurement_004: float, measurement_005: float, measurement_006: float, measurement_007: float,
):
    """8 ordered kalman updates; carry both state components between calls."""
    for measurement in (
        measurement_000, measurement_001, measurement_002, measurement_003, measurement_004,
        measurement_005, measurement_006, measurement_007,
    ):
        mean, variance = step(mean, variance, measurement, process_noise, measurement_noise)
    return mean, variance

def run_16(
    mean: float, variance: float, process_noise: float, measurement_noise: float,
    measurement_000: float, measurement_001: float, measurement_002: float, measurement_003: float,
    measurement_004: float, measurement_005: float, measurement_006: float, measurement_007: float,
    measurement_008: float, measurement_009: float, measurement_010: float, measurement_011: float,
    measurement_012: float, measurement_013: float, measurement_014: float, measurement_015: float,
):
    """16 ordered kalman updates; carry both state components between calls."""
    for measurement in (
        measurement_000, measurement_001, measurement_002, measurement_003, measurement_004,
        measurement_005, measurement_006, measurement_007, measurement_008, measurement_009,
        measurement_010, measurement_011, measurement_012, measurement_013, measurement_014,
        measurement_015,
    ):
        mean, variance = step(mean, variance, measurement, process_noise, measurement_noise)
    return mean, variance

def run_48(
    mean: float, variance: float, process_noise: float, measurement_noise: float,
    measurement_000: float, measurement_001: float, measurement_002: float, measurement_003: float,
    measurement_004: float, measurement_005: float, measurement_006: float, measurement_007: float,
    measurement_008: float, measurement_009: float, measurement_010: float, measurement_011: float,
    measurement_012: float, measurement_013: float, measurement_014: float, measurement_015: float,
    measurement_016: float, measurement_017: float, measurement_018: float, measurement_019: float,
    measurement_020: float, measurement_021: float, measurement_022: float, measurement_023: float,
    measurement_024: float, measurement_025: float, measurement_026: float, measurement_027: float,
    measurement_028: float, measurement_029: float, measurement_030: float, measurement_031: float,
    measurement_032: float, measurement_033: float, measurement_034: float, measurement_035: float,
    measurement_036: float, measurement_037: float, measurement_038: float, measurement_039: float,
    measurement_040: float, measurement_041: float, measurement_042: float, measurement_043: float,
    measurement_044: float, measurement_045: float, measurement_046: float, measurement_047: float,
):
    """48 ordered kalman updates; carry both state components between calls."""
    for measurement in (
        measurement_000, measurement_001, measurement_002, measurement_003, measurement_004,
        measurement_005, measurement_006, measurement_007, measurement_008, measurement_009,
        measurement_010, measurement_011, measurement_012, measurement_013, measurement_014,
        measurement_015, measurement_016, measurement_017, measurement_018, measurement_019,
        measurement_020, measurement_021, measurement_022, measurement_023, measurement_024,
        measurement_025, measurement_026, measurement_027, measurement_028, measurement_029,
        measurement_030, measurement_031, measurement_032, measurement_033, measurement_034,
        measurement_035, measurement_036, measurement_037, measurement_038, measurement_039,
        measurement_040, measurement_041, measurement_042, measurement_043, measurement_044,
        measurement_045, measurement_046, measurement_047,
    ):
        mean, variance = step(mean, variance, measurement, process_noise, measurement_noise)
    return mean, variance

def run_128(
    mean: float, variance: float, process_noise: float, measurement_noise: float,
    measurement_000: float, measurement_001: float, measurement_002: float, measurement_003: float,
    measurement_004: float, measurement_005: float, measurement_006: float, measurement_007: float,
    measurement_008: float, measurement_009: float, measurement_010: float, measurement_011: float,
    measurement_012: float, measurement_013: float, measurement_014: float, measurement_015: float,
    measurement_016: float, measurement_017: float, measurement_018: float, measurement_019: float,
    measurement_020: float, measurement_021: float, measurement_022: float, measurement_023: float,
    measurement_024: float, measurement_025: float, measurement_026: float, measurement_027: float,
    measurement_028: float, measurement_029: float, measurement_030: float, measurement_031: float,
    measurement_032: float, measurement_033: float, measurement_034: float, measurement_035: float,
    measurement_036: float, measurement_037: float, measurement_038: float, measurement_039: float,
    measurement_040: float, measurement_041: float, measurement_042: float, measurement_043: float,
    measurement_044: float, measurement_045: float, measurement_046: float, measurement_047: float,
    measurement_048: float, measurement_049: float, measurement_050: float, measurement_051: float,
    measurement_052: float, measurement_053: float, measurement_054: float, measurement_055: float,
    measurement_056: float, measurement_057: float, measurement_058: float, measurement_059: float,
    measurement_060: float, measurement_061: float, measurement_062: float, measurement_063: float,
    measurement_064: float, measurement_065: float, measurement_066: float, measurement_067: float,
    measurement_068: float, measurement_069: float, measurement_070: float, measurement_071: float,
    measurement_072: float, measurement_073: float, measurement_074: float, measurement_075: float,
    measurement_076: float, measurement_077: float, measurement_078: float, measurement_079: float,
    measurement_080: float, measurement_081: float, measurement_082: float, measurement_083: float,
    measurement_084: float, measurement_085: float, measurement_086: float, measurement_087: float,
    measurement_088: float, measurement_089: float, measurement_090: float, measurement_091: float,
    measurement_092: float, measurement_093: float, measurement_094: float, measurement_095: float,
    measurement_096: float, measurement_097: float, measurement_098: float, measurement_099: float,
    measurement_100: float, measurement_101: float, measurement_102: float, measurement_103: float,
    measurement_104: float, measurement_105: float, measurement_106: float, measurement_107: float,
    measurement_108: float, measurement_109: float, measurement_110: float, measurement_111: float,
    measurement_112: float, measurement_113: float, measurement_114: float, measurement_115: float,
    measurement_116: float, measurement_117: float, measurement_118: float, measurement_119: float,
    measurement_120: float, measurement_121: float, measurement_122: float, measurement_123: float,
    measurement_124: float, measurement_125: float, measurement_126: float, measurement_127: float,
):
    """128 ordered kalman updates; carry both state components between calls."""
    for measurement in (
        measurement_000, measurement_001, measurement_002, measurement_003, measurement_004,
        measurement_005, measurement_006, measurement_007, measurement_008, measurement_009,
        measurement_010, measurement_011, measurement_012, measurement_013, measurement_014,
        measurement_015, measurement_016, measurement_017, measurement_018, measurement_019,
        measurement_020, measurement_021, measurement_022, measurement_023, measurement_024,
        measurement_025, measurement_026, measurement_027, measurement_028, measurement_029,
        measurement_030, measurement_031, measurement_032, measurement_033, measurement_034,
        measurement_035, measurement_036, measurement_037, measurement_038, measurement_039,
        measurement_040, measurement_041, measurement_042, measurement_043, measurement_044,
        measurement_045, measurement_046, measurement_047, measurement_048, measurement_049,
        measurement_050, measurement_051, measurement_052, measurement_053, measurement_054,
        measurement_055, measurement_056, measurement_057, measurement_058, measurement_059,
        measurement_060, measurement_061, measurement_062, measurement_063, measurement_064,
        measurement_065, measurement_066, measurement_067, measurement_068, measurement_069,
        measurement_070, measurement_071, measurement_072, measurement_073, measurement_074,
        measurement_075, measurement_076, measurement_077, measurement_078, measurement_079,
        measurement_080, measurement_081, measurement_082, measurement_083, measurement_084,
        measurement_085, measurement_086, measurement_087, measurement_088, measurement_089,
        measurement_090, measurement_091, measurement_092, measurement_093, measurement_094,
        measurement_095, measurement_096, measurement_097, measurement_098, measurement_099,
        measurement_100, measurement_101, measurement_102, measurement_103, measurement_104,
        measurement_105, measurement_106, measurement_107, measurement_108, measurement_109,
        measurement_110, measurement_111, measurement_112, measurement_113, measurement_114,
        measurement_115, measurement_116, measurement_117, measurement_118, measurement_119,
        measurement_120, measurement_121, measurement_122, measurement_123, measurement_124,
        measurement_125, measurement_126, measurement_127,
    ):
        mean, variance = step(mean, variance, measurement, process_noise, measurement_noise)
    return mean, variance
