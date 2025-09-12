# Define the locations and their indices
locations = ['Home', 'Office', 'Store']
loc_to_idx = {loc: i for i, loc in enumerate(locations)}

# Define the travel time dictionary
travel_time_dict = {
    'Home': {'Office': 30, 'Store': 15},
    'Office': {'Home': 30, 'Store': 25},
    'Store': {'Home': 15, 'Office': 25},
}

# Initialize the travel time matrix with infinity (or a large number)
num_locations = len(locations)
travel_time_matrix = [[float('inf')] * num_locations for _ in range(num_locations)]

# Populate the travel time matrix
for from_loc in locations:
    for to_loc in locations:
        if from_loc != to_loc:  # Skip self-travel
            travel_time_matrix[loc_to_idx[from_loc]][loc_to_idx[to_loc]] = travel_time_dict[from_loc].get(to_loc, float('inf'))

# Optional: Print the matrix for verification
for row in travel_time_matrix:
    print(row)