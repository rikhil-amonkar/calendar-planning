import itertools
import json

# Define cities and their required durations
cities = {
    "Mykonos": 3,
    "Zurich": 5,
    "Prague": 3,
    "Riga": 5,
    "Bucharest": 5,
    "Valencia": 5,
    "Nice": 2
}

# Define direct flights as a set of tuples (city1, city2)
direct_flights = {
    ("Mykonos", "Nice"),
    ("Mykonos", "Zurich"),
    ("Prague", "Bucharest"),
    ("Valencia", "Bucharest"),
    ("Zurich", "Prague"),
    ("Riga", "Nice"),
    ("Zurich", "Riga"),
    ("Zurich", "Bucharest"),
    ("Zurich", "Valencia"),
    ("Bucharest", "Riga"),
    ("Prague", "Riga"),
    ("Prague", "Valencia"),
    ("Zurich", "Nice")
}

# Generate all permutations of cities, starting with Mykonos
city_list = list(cities.keys())
valid_itineraries = []

for perm in itertools.permutations(city_list):
    if perm[0] != "Mykonos":
        continue  # First city must be Mykonos
    valid = True
    for i in range(len(perm) - 1):
        if (perm[i], perm[i+1]) not in direct_flights and (perm[i+1], perm[i]) not in direct_flights:
            valid = False
            break
    if not valid:
        continue

    # Calculate start_day for each city
    start_days = {}
    current_day = 1
    for city in perm:
        start_days[city] = current_day
        current_day += cities[city]

    # Check constraints
    # Mykonos is first, days 1-3
    mykonos_start = start_days["Mykonos"]
    mykonos_duration = cities["Mykonos"]
    if mykonos_start != 1 or mykonos_duration != 3:
        continue

    # Prague must be visited between day 10 and 12
    prague_start = start_days["Prague"]
    prague_duration = cities["Prague"]
    prague_end = prague_start + prague_duration - 1
    if not (10 <= prague_start <= 12 and 10 <= prague_end <= 12):
        continue

    # Total days should be 28
    total_days = current_day - 1
    if total_days != 28:
        continue

    valid_itineraries.append(perm)

# Output the first valid itinerary
if valid_itineraries:
    itinerary = valid_itineraries[0]
    result = {"itinerary": []}
    current_day = 1
    for city in itinerary:
        duration = cities[city]
        day_range = f"Day {current_day}-{current_day + duration - 1}"
        result["itinerary"].append({"day_range": day_range, "place": city})
        current_day += duration
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))