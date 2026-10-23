def cascade_step(x: float, y: float, observation: float) -> tuple[float, float]:
    x = (x + observation) / 2.0
    y = (y + observation) / 2.0
    x = (x + observation) / 2.0
    y = (y + observation) / 2.0
    x = (x + observation) / 2.0
    y = (y + observation) / 2.0
    x = (x + observation) / 2.0
    y = (y + observation) / 2.0
    return x, y


def cascade_4(x, y, z000, z001, z002, z003):
    for observation in (z000, z001, z002, z003):
        x, y = cascade_step(x, y, observation)
    return x, y


def cascade_32(
    x, y, z000, z001, z002, z003, z004, z005, z006, z007, z008, z009, z010, z011, z012,
    z013, z014, z015, z016, z017, z018, z019, z020, z021, z022, z023, z024, z025, z026,
    z027, z028, z029, z030, z031
):
    for observation in (
        z000, z001, z002, z003, z004, z005, z006, z007, z008, z009, z010, z011, z012,
        z013, z014, z015, z016, z017, z018, z019, z020, z021, z022, z023, z024, z025,
        z026, z027, z028, z029, z030, z031
    ):
        x, y = cascade_step(x, y, observation)
    return x, y


def cascade_64(
    x, y, z000, z001, z002, z003, z004, z005, z006, z007, z008, z009, z010, z011, z012,
    z013, z014, z015, z016, z017, z018, z019, z020, z021, z022, z023, z024, z025, z026,
    z027, z028, z029, z030, z031, z032, z033, z034, z035, z036, z037, z038, z039, z040,
    z041, z042, z043, z044, z045, z046, z047, z048, z049, z050, z051, z052, z053, z054,
    z055, z056, z057, z058, z059, z060, z061, z062, z063
):
    for observation in (
        z000, z001, z002, z003, z004, z005, z006, z007, z008, z009, z010, z011, z012,
        z013, z014, z015, z016, z017, z018, z019, z020, z021, z022, z023, z024, z025,
        z026, z027, z028, z029, z030, z031, z032, z033, z034, z035, z036, z037, z038,
        z039, z040, z041, z042, z043, z044, z045, z046, z047, z048, z049, z050, z051,
        z052, z053, z054, z055, z056, z057, z058, z059, z060, z061, z062, z063
    ):
        x, y = cascade_step(x, y, observation)
    return x, y
