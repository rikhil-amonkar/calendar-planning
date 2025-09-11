import itertools
import json

# Define the cities and their required durations
cities = ['Venice', 'Mykonos', 'Vienna']
durations = {
    'Venice': 6,
    'Mykonos': 2,
    'Vienna': 4
}

# Define direct flight connections (bidirectional)
direct_flights = {('Mykonos', 'Vienna'), ('Vienna', 'Mykonos'), 
                  ('Vienna', 'Venice'), ('Venice', 'Vienna')}

# Generate all permutations of cities and check for valid itineraries
for perm in itertools.permutations(cities):
    valid_sequence = True
    # Check if consecutive cities have direct flights
    for i in range(len(perm) - 1):
        if (perm[i], perm[i+1]) not in direct_flights:
            valid_sequence = False
            break
    if not valid_sequence:
        continue
    
    # Calculate day ranges for each city in the sequence
    current_day = 1
    itinerary_data = []
    for city in perm:
        dur = durations[city]
        end_day = current_day + dur - 1
        itinerary_data.append((current_day, end_day, city))
        current_day = end_day
    
    # Ensure the total trip duration is correct (last day is 10)
    if itinerary_data[-1][1] != 10:
        continue
    
    # Check if Venice's stay includes days between 5-10
    venice_entry = None
    for entry in itinerary_data:
        if entry[2] == 'Venice':
            venice_entry = entry
            break
    venice_start, venice_end, _ = venice_entry
    if venice_end >= 5 and venice_start <= 10:
        # Construct the JSON output
        itinerary = []
        for start, end, place in itinerary_data:
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": place})
        result = {"itinerary": itinerary}
        print(json.dumps(result))
        exit()

# If no valid itinerary is found (should not happen with given constraints)
print(json.dumps({"error": "No valid itinerary found"}))