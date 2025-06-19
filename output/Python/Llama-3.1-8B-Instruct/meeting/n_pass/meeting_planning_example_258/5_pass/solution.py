def calculate_travel_time(current_location, location, travel_times):
    """
    Calculate the travel time from the current location to the next location.

    Args:
    current_location (str): The current location.
    location (str): The next location.
    travel_times (dict): A dictionary containing travel times.
        Each key in the dictionary represents a location.
        Each value is another dictionary where the keys are the neighboring locations
        and the values are the travel times.

    Returns:
    float: The travel time from the current location to the next location.

    Raises:
    TypeError: If travel_times is not a dictionary or if the travel times are not numeric.
    KeyError: If current_location or location is not a key in travel_times or if location is not a key in travel_times[current_location].
    ValueError: If travel_times[current_location][location] is not a numeric value.
    """

    # Check if travel_times is a dictionary
    if not isinstance(travel_times, dict):
        raise TypeError("travel_times must be a dictionary")

    # Check if current_location and location are keys in travel_times
    if current_location not in travel_times:
        raise KeyError(f"Invalid current location. Current location: {current_location}")

    # Check if location is a key in travel_times[current_location]
    if location not in travel_times[current_location]:
        raise KeyError(f"Invalid location. Current location: {current_location}, Location: {location}")

    # Get the travel time from the current location to the next location
    travel_time = travel_times[current_location][location]

    # Check if travel_time is numeric
    if not isinstance(travel_time, (int, float)):
        raise ValueError(f"Travel time must be numeric. Current location: {current_location}, Location: {location}")

    return travel_time

# Example usage
travel_times = {
    'A': {'B': 10, 'C': 20},
    'B': {'A': 10, 'C': 15},
    'C': {'A': 20, 'B': 15}
}

current_location = 'A'
location = 'B'
print(calculate_travel_time(current_location, location, travel_times))  # Output: 10

# Test error handling
try:
    print(calculate_travel_time('D', 'B', travel_times))
except KeyError as e:
    print(e)

try:
    print(calculate_travel_time('A', 'D', travel_times))
except KeyError as e:
    print(e)

try:
    print(calculate_travel_time('A', 'B', {'A': {'B': 'ten'}}))
except ValueError as e:
    print(e)