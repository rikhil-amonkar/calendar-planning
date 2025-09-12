# Define the locations of each friend (index 0 to 4)
friends_locations = ['Home', 'Office', 'Park', 'School', 'Gym']

# Initialize a 5x5 travel time matrix
travel_time_matrix = [[0 for _ in range(5)] for _ in range(5)]

# Example travel_time dictionary (you can replace this with real data)
travel_time = {
    'Home': {'Office': 15, 'Park': 10, 'School': 20, 'Gym': 5},
    'Office': {'Home': 15, 'Park': 25, 'School': 10, 'Gym': 30},
    'Park': {'Home': 10, 'Office': 25, 'School': 12, 'Gym': 18},
    'School': {'Home': 20, 'Office': 10, 'Park': 12, 'Gym': 22},
    'Gym': {'Home': 5, 'Office': 30, 'Park': 18, 'School': 22}
}

# Populate the travel time matrix
for k in range(5):
    for m in range(5):
        loc_k = friends_locations[k]
        loc_m = friends_locations[m]
        if loc_k == loc_m:
            travel_time_matrix[k][m] = 0
        else:
            travel_time_matrix[k][m] = travel_time[loc_k][loc_m]

# Optional: print the matrix
for row in travel_time_matrix:
    print(row)