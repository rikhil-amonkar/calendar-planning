def calculate_travel_time(current_location, location, travel_times):
    # Get the travel time from the current location to the next location
    return travel_times[current_location][location]