import json
from itertools import permutations

# Input parameters
total_days = 12
required_days = {
    "Riga": 5,
    "Vilnius": 7,
    "Dublin": 2
}
flight_graph = {
    "Dublin": ["Riga"],
    "Riga": ["Dublin", "Vilnius"],
    "Vilnius": []
}

# Find valid sequence through all cities
def find_valid_route():
    cities = ["Dublin", "Riga", "Vilnius"]
    for perm in permutations(cities):
        valid = True
        for i in range(len(perm)-1):
            if perm[i+1] not in flight_graph[perm[i]]:
                valid = False
                break
        if valid:
            return list(perm)
    return None

# Calculate itinerary
def calculate_itinerary(sequence):
    itinerary = []
    current_day = 1
    for city in sequence:
        needed = required_days[city]
        end_day = current_day + needed - 1
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        current_day = end_day
    return itinerary

# Main logic
valid_sequence = find_valid_route()
if not valid_sequence or calculate_itinerary(valid_sequence)[-1]["day_range"].split("-")[-1] != f"{total_days}":
    result = {"itinerary": []}
else:
    result = {"itinerary": calculate_itinerary(valid_sequence)}

print(json.dumps(result))