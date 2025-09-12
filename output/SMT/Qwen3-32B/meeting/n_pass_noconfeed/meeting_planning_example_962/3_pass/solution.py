# Sample data: list of friends with their locations
friends = [
    {'name': 'Alice', 'location': 'Home'},
    {'name': 'Bob', 'location': 'Office'},
    {'name': 'Charlie', 'location': 'Cafe'}
]

# Predefined travel times between locations
travel_times = {
    'Home': {'Home': 0, 'Office': 15, 'Cafe': 10},
    'Office': {'Home': 15, 'Office': 0, 'Cafe': 20},
    'Cafe': {'Home': 10, 'Office': 20, 'Cafe': 0}
}

# Precompute travel times between friends
friend_locations = [f['location'] for f in friends]
num_friends = len(friends)
travel_time_between = [[0] * num_friends for _ in range(num_friends)]

for j in range(num_friends):
    for k in range(num_friends):
        loc_j = friend_locations[j]
        loc_k = friend_locations[k]
        if loc_j == loc_k:
            travel_time_between[j][k] = 0
        else:
            travel_time_between[j][k] = travel_times[loc_j][loc_k]

# Optional: print the travel time matrix
for row in travel_time_between:
    print(row)