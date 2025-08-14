import itertools
import json

# Define input parameters
cities = ['Vilnius', 'Munich', 'Mykonos']
durations = {'Vilnius': 4, 'Munich': 3, 'Mykonos': 7}
total_days = 12
allowed_edges = [frozenset({'Vilnius', 'Munich'}), frozenset({'Munich', 'Mykonos'})]

# Find a valid permutation of cities with direct flights between consecutive cities
valid_perm = None
for perm in itertools.permutations(cities):
    valid = True
    for i in range(len(perm) - 1):
        current, next_city = perm[i], perm[i + 1]
        if frozenset({current, next_city}) not in allowed_edges:
            valid = False
            break
    if valid:
        # Check if the durations satisfy the total days constraint
        sum_d = sum(durations[city] for city in cities)
        transitions = len(perm) - 1
        if sum_d - transitions == total_days:
            valid_perm = perm
            break

# Generate the itinerary based on the valid permutation
itinerary = []
current_start = 1
for city in valid_perm:
    d = durations[city]
    current_end = current_start + d - 1
    day_range = f"Day {current_start}-{current_end}"
    itinerary.append({"day_range": day_range, "place": city})
    current_start = current_end  # Next city starts on the same day as the previous ends

# Prepare and print the JSON output
result = {"itinerary": itinerary}
print(json.dumps(result))