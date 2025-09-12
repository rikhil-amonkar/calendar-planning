import itertools

# Define a complete travel time matrix between all locations
travel_times = {
    'Presidio': {
        'SFO': 15,
        'San Francisco': 10,
        'Oakland': 30
    },
    'SFO': {
        'Presidio': 15,
        'San Francisco': 20,
        'Oakland': 30
    },
    'San Francisco': {
        'Presidio': 10,
        'SFO': 20,
        'Oakland': 25
    },
    'Oakland': {
        'Presidio': 30,
        'SFO': 30,
        'San Francisco': 25
    }
}

# List of friends and their locations
friends = [
    {'location': 'SFO'},
    {'location': 'San Francisco'},
    {'location': 'Oakland'}
]

# Extract just the locations
locations = [friend['location'] for friend in friends]

# Initialize variables to track the optimal route and time
best_route = None
min_total_time = float('inf')

# Try all permutations of the friends' locations
for perm in itertools.permutations(locations):
    # Start at Presidio
    total_time = travel_times['Presidio'][perm[0]]
    
    # Add travel time between each consecutive pair in the permutation
    for i in range(len(perm) - 1):
        total_time += travel_times[perm[i]][perm[i + 1]]
    
    # Update best route if this one is better
    if total_time < min_total_time:
        min_total_time = total_time
        best_route = perm

# Output the optimal route and total travel time
print(f"Optimal route: Presidio -> {' -> '.join(best_route)}")
print(f"Total travel time: {min_total_time} minutes")