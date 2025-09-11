import json

# Define constraints
madrid_start = 1
madrid_duration = 7  # 7 days in Madrid
madrid_end = madrid_start + madrid_duration - 1

bucharest_start = 14
bucharest_duration = 2  # 2 days in Bucharest
bucharest_end = bucharest_start + bucharest_duration - 1

seville_duration = 3
paris_duration = 6

# Calculate Seville's start and end
seville_start = madrid_end  # starts the same day Madrid ends
seville_end = seville_start + seville_duration - 1

# Calculate Paris's start and end
paris_start = seville_end  # starts the same day Seville ends
paris_end = paris_start + paris_duration - 1

# Create the visits list
visits = [
    {'city': 'Madrid', 'start': madrid_start, 'end': madrid_end},
    {'city': 'Seville', 'start': seville_start, 'end': seville_end},
    {'city': 'Paris', 'start': paris_start, 'end': paris_end},
    {'city': 'Bucharest', 'start': bucharest_start, 'end': bucharest_end}
]

# Check if transitions are valid (direct flights)
flights_available = {
    'Madrid': ['Paris', 'Seville', 'Bucharest'],
    'Paris': ['Madrid', 'Seville', 'Bucharest'],
    'Seville': ['Madrid', 'Paris'],
    'Bucharest': ['Madrid', 'Paris']
}

valid_transitions = True
for i in range(len(visits) - 1):
    current_city = visits[i]['city']
    next_city = visits[i+1]['city']
    if next_city not in flights_available[current_city]:
        valid_transitions = False
        break

if not valid_transitions:
    print("No valid itinerary found with the given constraints.")
else:
    # Generate the itinerary JSON
    itinerary = []
    for visit in visits:
        day_range = f"Day {visit['start']}-{visit['end']}"
        itinerary.append({"day_range": day_range, "place": visit['city']})
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))