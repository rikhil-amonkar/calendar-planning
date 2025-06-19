def calculate_travel_time(current_location, location, travel_times):
    """
    Calculate the travel time from the current location to the next location.

    Args:
    current_location (str): The current location.
    location (str): The next location.
    travel_times (dict): A dictionary containing travel times.

    Returns:
    float: The travel time from the current location to the next location.

    Raises:
    TypeError: If travel_times is not a dictionary.
    KeyError: If current_location or location is not a key in travel_times.
    """

    # Check if travel_times is a dictionary
    if not isinstance(travel_times, dict):
        raise TypeError("travel_times must be a dictionary")

    # Check if current_location and location are keys in travel_times
    if current_location not in travel_times or location not in travel_times[current_location]:
        raise KeyError(f"Invalid location. Current location: {current_location}, Location: {location}")

    # Get the travel time from the current location to the next location
    return travel_times[current_location][location]

# Example usage
travel_times = {
    'A': {'B': 10, 'C': 20},
    'B': {'A': 10, 'C': 15},
    'C': {'A': 20, 'B': 15}
}

current_location = 'A'
location = 'B'
print(calculate_travel_time(current_location, location, travel_times))  # Output: 10