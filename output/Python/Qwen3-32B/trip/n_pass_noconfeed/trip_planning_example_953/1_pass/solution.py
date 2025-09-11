import json
from itertools import permutations

# Define the required days for each city
cities = {
    'Venice': 5,
    'Barcelona': 2,
    'Stuttgart': 3,
    'Frankfurt': 4,
    'Salzburg': 4,
    'Florence': 4,
    'Stockholm': 2
}

# Define direct flight connections
flights = {
    'Venice': ['Barcelona', 'Stuttgart', 'Frankfurt'],
    'Barcelona': ['Frankfurt', 'Florence', 'Stockholm', 'Stuttgart', 'Venice'],
    'Stuttgart': ['Barcelona', 'Frankfurt', 'Stockholm', 'Venice'],
    'Frankfurt': ['Barcelona', 'Florence', 'Salzburg', 'Stockholm', 'Stuttgart', 'Venice'],
    'Salzburg': ['Frankfurt'],
    'Florence': ['Frankfurt', 'Barcelona'],
    'Stockholm': ['Barcelona', 'Frankfurt', 'Stuttgart']
}

# Generate all permutations of the remaining cities after Venice
remaining_cities = ['Barcelona', 'Stuttgart', 'Frankfurt', 'Salzburg', 'Florence', 'Stockholm']
found = False

for perm in permutations(remaining_cities):
    sequence = ['Venice'] + list(perm)
    valid = True
    for i in range(len(sequence) - 1):
        current = sequence[i]
        next_city = sequence[i + 1]
        if next_city not in flights[current]:
            valid = False
            break
    if valid:
        # Calculate the day ranges
        itinerary = []
        current_day = 1
        for city in sequence:
            days_needed = cities[city]
            end_day = current_day + days_needed - 1
            itinerary.append({
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            })
            current_day = end_day + 1  # Next city starts the day after the previous one ends
        # Check if total days is 18
        if current_day - 1 == 18:
            print(json.dumps({"itinerary": itinerary}))
            found = True
            break

if not found:
    print(json.dumps({"error": "No valid itinerary found"}))