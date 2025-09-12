# Sample travel time dictionary
travel_time_dict = {
    'A': {'B': 10, 'C': 20},
    'B': {'A': 10, 'C': 15},
    'C': {'A': 20, 'B': 15}
}

# Define locations from the keys
locations = list(travel_time_dict.keys())

# Create a mapping from location to matrix index
loc_to_idx = {loc: idx for idx, loc in enumerate(locations)}

# Initialize the travel time matrix with zeros
n_locations = len(locations)
travel_time_matrix = [[0] * n_locations for _ in range(n_locations)]

# Populate the matrix
for from_loc in locations:
    for to_loc in locations:
        if from_loc == to_loc:
            travel_time_matrix[loc_to_idx[from_loc]][loc_to_idx[to_loc]] = 0
        else:
            travel_time_matrix[loc_to_idx[from_loc]][loc_to_idx[to_loc]] = travel_time_dict[from_loc][to_loc]

# Resulting matrix:
# [
#   [0, 10, 20],
#   [10, 0, 15],
#   [20, 15, 0]
# ]