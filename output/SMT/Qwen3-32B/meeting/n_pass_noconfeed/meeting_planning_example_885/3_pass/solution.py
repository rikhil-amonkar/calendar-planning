# Example data (replace with your actual data)
friend_locations = ['Home', 'Office', 'Park', 'School', 'Cafe', 'Library', 'Gym', 'Mall', 'Airport']
travel_times = {
    ('Home', 'Office'): 15,
    ('Home', 'Park'): 10,
    # Add all required travel times
}

# Initialize the result matrix
travel_time_between_friends = []

for i in range(9):
    row = []
    for j in range(9):
        loc_i = friend_locations[i]
        loc_j = friend_locations[j]
        if loc_i == loc_j:
            row.append(0)
        else:
            row.append(travel_times.get((loc_i, loc_j), float('inf')))  # Use default if not found
    travel_time_between_friends.append(row)