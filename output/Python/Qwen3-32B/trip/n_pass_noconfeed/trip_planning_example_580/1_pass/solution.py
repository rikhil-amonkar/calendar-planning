import json
from itertools import permutations

# Define durations for each city
durations = {
    'Paris': 6,
    'Oslo': 5,
    'Porto': 7,
    'Geneva': 7,
    'Reykjavik': 2
}

# Direct flight connections
direct_flights = {
    'Paris': ['Oslo', 'Geneva', 'Porto', 'Reykjavik'],
    'Oslo': ['Paris', 'Geneva', 'Porto', 'Reykjavik'],
    'Porto': ['Paris', 'Oslo', 'Geneva'],
    'Geneva': ['Oslo', 'Paris', 'Porto'],
    'Reykjavik': ['Paris', 'Oslo']
}

# Constraints for Geneva and Oslo
geneva_start, geneva_end = 1, 7  # 7 days
oslo_start, oslo_end = 19, 23    # 5 days

# Find valid permutations for the three cities between Geneva and Oslo
middle_cities = ['Paris', 'Porto', 'Reykjavik']
valid_permutations = []

for perm in permutations(middle_cities):
    valid = True
    # Check transitions between consecutive cities in the permutation
    for i in range(len(perm) - 1):
        if perm[i+1] not in direct_flights[perm[i]]:
            valid = False
            break
    # Check transition from last city in permutation to Oslo
    if 'Oslo' not in direct_flights[perm[-1]]:
        valid = False
    if valid:
        valid_permutations.append(perm)

# Assume there's at least one valid permutation
itinerary = []

if valid_permutations:
    # Take the first valid permutation
    perm = valid_permutations[0]
    
    # Compute day ranges for the middle cities
    current_day = geneva_end  # Start after Geneva ends (day 7)
    middle_segments = []
    
    for city in perm:
        start_day = current_day
        end_day = start_day + durations[city] - 1
        middle_segments.append({
            'city': city,
            'start': start_day,
            'end': end_day
        })
        current_day = end_day  # next city starts on this day
    
    # Add Geneva to the itinerary
    itinerary.append({
        'day_range': f"Day {geneva_start}-{geneva_end}",
        'place': 'Geneva'
    })
    
    # Add middle cities
    for seg in middle_segments:
        itinerary.append({
            'day_range': f"Day {seg['start']}-{seg['end']}",
            'place': seg['city']
        })
    
    # Add Oslo to the itinerary
    itinerary.append({
        'day_range': f"Day {oslo_start}-{oslo_end}",
        'place': 'Oslo'
    })

# Output as JSON
result = {'itinerary': itinerary}
print(json.dumps(result, indent=2))