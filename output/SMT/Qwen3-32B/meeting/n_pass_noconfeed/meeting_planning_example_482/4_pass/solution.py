travel_times = [
    [0, 11, 18, 12, 17, 23],
    [12, 0, 15, 16, 15, 22],
    [19, 13, 0, 23, 23, 25],
    [11, 15, 22, 0, 7, 13],
    [17, 16, 23, 7, 0, 7],
    [22, 22, 26, 12, 7, 0]
]

# Example values for demonstration
prev_loc = 1  # Previous location index
current_loc = 3  # Current location index

# Calculate travel time between locations
travel_time_step = travel_times[prev_loc][current_loc]

print(f"Travel time from location {prev_loc} to {current_loc}: {travel_time_step} minutes")