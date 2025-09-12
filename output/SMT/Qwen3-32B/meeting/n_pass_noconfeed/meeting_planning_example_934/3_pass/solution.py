# Sample data for friends (each with a location)
friends = [
    {"location": "Home"},
    {"location": "Office"},
    {"location": "Gym"}
]

# Sample travel times between locations
travel_times = {
    ("Home", "Office"): 15,
    ("Office", "Home"): 15,
    ("Home", "Gym"): 10,
    ("Gym", "Home"): 10,
    ("Office", "Gym"): 20,
    ("Gym", "Office"): 20
}

# Initialize the travel time matrix
travel_time_matrix = []

# Populate the matrix
for i in range(len(friends)):
    row = []
    for j in range(len(friends)):
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        if loc_i == loc_j:
            row.append(0)  # No travel time to self
        else:
            row.append(travel_times[(loc_i, loc_j)])
    travel_time_matrix.append(row)

# Optional: Print the result
for row in travel_time_matrix:
    print(row)