import itertools
import json

# Define cities and their required durations
cities = ["Warsaw", "Budapest", "Paris", "Riga"]
durations = {
    "Warsaw": 2,
    "Budapest": 7,
    "Paris": 4,
    "Riga": 7
}

# Define direct flight connections
direct_flights = {
    "Warsaw": ["Budapest", "Riga", "Paris"],
    "Budapest": ["Warsaw", "Paris"],
    "Paris": ["Warsaw", "Budapest", "Riga"],
    "Riga": ["Warsaw", "Paris"]
}

# Generate all permutations where the first city is Warsaw
for perm in itertools.permutations(cities):
    if perm[0] != "Warsaw":
        continue
    
    # Check if all consecutive cities have direct flights
    valid = True
    for i in range(len(perm) - 1):
        current = perm[i]
        next_city = perm[i + 1]
        if next_city not in direct_flights[current]:
            valid = False
            break
    if not valid:
        continue

    # Calculate start days for each city
    start_days = [1]  # Start of the first city
    for i in range(len(perm) - 1):
        prev_start = start_days[i]
        prev_duration = durations[perm[i]]
        next_start = prev_start + prev_duration - 1
        start_days.append(next_start)

    # Check if Riga starts on day 11
    riga_index = perm.index("Riga")
    if start_days[riga_index] == 11:
        # Construct the itinerary
        itinerary = []
        for i in range(len(perm)):
            city = perm[i]
            start = start_days[i]
            duration = durations[city]
            end = start + duration - 1
            day_range = f"Day {start}-Day {end}"
            itinerary.append({"day_range": day_range, "place": city})
        # Output the result as JSON
        print(json.dumps({"itinerary": itinerary}))
        break