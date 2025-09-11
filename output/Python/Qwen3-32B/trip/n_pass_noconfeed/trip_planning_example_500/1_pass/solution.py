import itertools
import json

# Define parameters
durations = {
    'Hamburg': 7,
    'Munich': 6,
    'Manchester': 2,
    'Lyon': 2,
    'Split': 7
}
fixed_positions = {
    'Lyon': 13,
    'Manchester': 19
}
direct_flights = {
    'Hamburg': ['Munich', 'Manchester', 'Split'],
    'Munich': ['Hamburg', 'Split', 'Manchester', 'Lyon'],
    'Split': ['Hamburg', 'Munich', 'Lyon', 'Manchester'],
    'Lyon': ['Munich', 'Split'],
    'Manchester': ['Munich', 'Hamburg', 'Split']
}

# Generate all permutations of the first four cities (excluding Manchester)
for perm in itertools.permutations(['Hamburg', 'Munich', 'Split', 'Lyon']):
    # Check transitions between consecutive cities in the permutation
    valid_transitions = True
    for i in range(len(perm) - 1):
        current = perm[i]
        next_city = perm[i+1]
        if next_city not in direct_flights[current]:
            valid_transitions = False
            break
    if not valid_transitions:
        continue
    
    # Check transition from last city in permutation to Manchester
    last_in_perm = perm[-1]
    if 'Manchester' not in direct_flights[last_in_perm]:
        continue
    
    # Calculate start and end days for each city in the permutation
    start_days = {}
    end_days = {}
    current_start = 1
    for city in perm:
        start_days[city] = current_start
        duration = durations[city]
        end_days[city] = current_start + duration - 1
        current_start = end_days[city]  # next city starts on this day
    
    # Check if Lyon's start day is correct and Manchester's start day is correct
    if start_days.get('Lyon', 0) == fixed_positions['Lyon'] and current_start == fixed_positions['Manchester']:
        # Build the itinerary
        itinerary = []
        for city in perm:
            start = start_days[city]
            end = end_days[city]
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
        # Add Manchester
        start_man = current_start
        end_man = start_man + durations['Manchester'] - 1
        itinerary.append({"day_range": f"Day {start_man}-{end_man}", "place": "Manchester"})
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
        exit()

# If no valid itinerary found
print(json.dumps({"error": "No valid itinerary found"}))