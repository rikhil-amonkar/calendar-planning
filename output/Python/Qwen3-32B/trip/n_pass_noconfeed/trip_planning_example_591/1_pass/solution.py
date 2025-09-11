import itertools
import json

# Define cities and their durations
cities = {
    "Stuttgart": 2,
    "Bucharest": 2,
    "Geneva": 4,
    "Valencia": 6,
    "Munich": 7
}

# Direct flights as a set of tuples (city1, city2)
direct_flights = {
    ("Geneva", "Munich"),
    ("Munich", "Geneva"),
    ("Munich", "Valencia"),
    ("Valencia", "Munich"),
    ("Bucharest", "Valencia"),
    ("Valencia", "Bucharest"),
    ("Munich", "Bucharest"),
    ("Bucharest", "Munich"),
    ("Valencia", "Stuttgart"),
    ("Stuttgart", "Valencia"),
    ("Geneva", "Valencia"),
    ("Valencia", "Geneva")
}

# Generate all permutations of the 5 cities
all_perms = itertools.permutations(cities.keys())

valid_itineraries = []

for perm in all_perms:
    # Check if consecutive cities have direct flights
    valid_path = True
    for i in range(len(perm) - 1):
        if (perm[i], perm[i+1]) not in direct_flights:
            valid_path = False
            break
    if not valid_path:
        continue

    # Calculate start and end days for each city in the permutation
    # Total duration is sum of durations minus number of transitions (4) = 17
    # We need to find the start day of the first city such that the last city ends on day 17
    total_duration = sum(cities[c] for c in cities)
    num_transitions = len(perm) - 1
    expected_total_days = total_duration - num_transitions
    if expected_total_days != 17:
        continue  # This should not happen as per problem constraints

    # Calculate start day of the first city
    # The end day of the last city is 17
    # The end day of the last city is start_day + sum_durations - 1
    # So start_day = 17 - (sum_durations - 1) = 17 - 21 + 1 = -3
    # But this is negative, so no solution?
    # Wait, this suggests no solution, but the problem states there is one.
    # Let's try to work backward from the end to find possible start days

    # Work backward to calculate start days
    # Start with the last city, which ends on day 17
    end_days = {}
    start_days = {}
    current_end = 17
    for city in reversed(perm):
        duration = cities[city]
        start_days[city] = current_end - duration + 1
        end_days[city] = current_end
        current_end = start_days[city] - 1

    # Check if all start_days are positive
    all_positive = all(start_days[c] > 0 for c in perm)
    if not all_positive:
        continue

    # Check Geneva's start day is between 1 and 4
    geneva_start = start_days.get("Geneva", 0)
    if not (1 <= geneva_start <= 4):
        continue

    # Check Munich's start day is between 4 and 10
    munich_start = start_days.get("Munich", 0)
    if not (4 <= munich_start <= 10):
        continue

    # Build the itinerary
    itinerary = []
    for i in range(len(perm) - 1):
        start = start_days[perm[i]]
        end = end_days[perm[i]]
        next_start = start_days[perm[i+1]]
        # The next city starts on next_start, which is end + 1
        # So the day range for current city is start to end
        day_range = f"Day {start}-{end+1}"
        itinerary.append({"day_range": day_range, "place": perm[i]})
    # Add the last city
    last_start = start_days[perm[-1]]
    last_end = end_days[perm[-1]]
    day_range = f"Day {last_start}-{last_end}"
    itinerary.append({"day_range": day_range, "place": perm[-1]})

    valid_itineraries.append({"itinerary": itinerary})
    break  # Assuming we only need one valid solution

# Output the result as JSON
if valid_itineraries:
    print(json.dumps(valid_itineraries[0], indent=2))
else:
    print(json.dumps({"itinerary": []}))