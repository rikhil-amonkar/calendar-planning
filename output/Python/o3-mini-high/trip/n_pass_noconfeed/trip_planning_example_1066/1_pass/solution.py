import json
import itertools

# Trip constraints as input variables
total_trip_days = 21

# Cities with required durations (in days)
city_durations = {
    "Brussels": 4,
    "Bucharest": 3,
    "Stuttgart": 4,
    "Mykonos": 2,
    "Madrid": 2,
    "Helsinki": 5,
    "Split": 3,
    "London": 5
}

# Direct flight connections (each pair is bidirectional)
direct_flights = [
    ("Helsinki", "London"),
    ("Split", "Madrid"),
    ("Helsinki", "Madrid"),
    ("London", "Madrid"),
    ("Brussels", "London"),
    ("Bucharest", "London"),
    ("Brussels", "Bucharest"),
    ("Bucharest", "Madrid"),
    ("Split", "Helsinki"),
    ("Mykonos", "Madrid"),
    ("Stuttgart", "London"),
    ("Helsinki", "Brussels"),
    ("Brussels", "Madrid"),
    ("Split", "London"),
    ("Stuttgart", "Split"),
    ("London", "Mykonos")
]

# Build the flight graph as an adjacency list (bidirectional)
flight_graph = {}
for city1, city2 in direct_flights:
    flight_graph.setdefault(city1, set()).add(city2)
    flight_graph.setdefault(city2, set()).add(city1)

# Function to compute start days for each city's segment given an order.
# The rule: if you fly from A to B on day X, you are in both A and B on that day.
# Thus, the first city is visited from day 1 to day (duration_A).
# For subsequent cities, start_day = previous start_day + (duration(previous) - 1).
def compute_start_days(order, durations):
    start_days = []
    current_day = 1
    for city in order:
        start_days.append(current_day)
        current_day = current_day + durations[city] - 1
    return start_days

# Constraint check:
# 1. Madrid must be the final city (for conference on day 20-21)
# 2. For every adjacent city pair in the order, there must be a direct flight.
# 3. The overall trip must last 21 days.
#    (The sum of all durations is constant; note that total unique days = (sum(durations) - (#flights)) ).
# 4. Friend meeting in Stuttgart must occur between day 1 and day 4.
#    That is, if Stuttgart appears in the order, its start day must be <= 4.
# 5. Moreover, since Madrid is visited for 2 days and the conference is on day 20-21,
#    the Madrid segment must start exactly on day 20.
cities = list(city_durations.keys())

valid_order = None

# We force Madrid to be last
for perm in itertools.permutations(cities):
    if perm[-1] != "Madrid":
        continue

    # Check that every consecutive pair has a direct flight.
    valid_route = True
    for i in range(len(perm) - 1):
        if perm[i+1] not in flight_graph.get(perm[i], set()):
            valid_route = False
            break
    if not valid_route:
        continue

    # Compute cumulative start days based on the overlapping flight rule.
    start_days = compute_start_days(perm, city_durations)
    # The final day of the trip is: start_day(last) + duration(last) - 1.
    final_day = start_days[-1] + city_durations[perm[-1]] - 1
    if final_day != total_trip_days:
        continue

    # Check friend meeting constraint: Stuttgart's segment must include a day <=4.
    for idx, city in enumerate(perm):
        if city == "Stuttgart":
            if start_days[idx] > 4:
                valid_route = False
                break
    if not valid_route:
        continue

    # Check Madrid's timing: since it is last and lasts 2 days, it must start on day 20 so that days 20 and 21 are in Madrid.
    if start_days[-1] != 20:
        continue

    # If all checks pass, we found a valid ordering.
    valid_order = (perm, start_days)
    break

# If a valid itinerary is found, build a JSON output
if valid_order is not None:
    order, start_days = valid_order
    itinerary = []
    for idx, city in enumerate(order):
        start_day = start_days[idx]
        end_day = start_day + city_durations[city] - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
    output = {"itinerary": itinerary}
else:
    output = {"itinerary": []}

print(json.dumps(output))