from datetime import timedelta

def calculate_travel_time(start_location, end_location):
    """
    Calculate the travel time between two locations.

    Args:
        start_location (str): The starting location.
        end_location (str): The ending location.

    Returns:
        datetime.timedelta: The travel time between the two locations. If the travel time is not found, returns a timedelta with 0 minutes.

    Raises:
        ValueError: If the start_location or end_location is not a string.
        KeyError: If the travel time is not found in the dictionary.
    """
    if not isinstance(start_location, str) or not isinstance(end_location, str):
        raise ValueError("Start and end locations must be strings")

    travel_time = travel_distances.get((start_location, end_location))
    if travel_time is None:
        travel_time = travel_distances.get((end_location, start_location))
    if travel_time is None:
        raise KeyError(f"Travel time not found for locations {start_location} and {end_location}")

    return timedelta(minutes=travel_time)