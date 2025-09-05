import itertools
import json

# Define the cities and their required durations (in days)
cities = ["Dublin", "Krakow", "Istanbul", "Venice", "Naples", "Brussels", "Mykonos", "Frankfurt"]
durations = {
    "Dublin": 5,
    "Krakow": 4,
    "Istanbul": 3,
    "Venice": 3,
    "Naples": 4,
    "Brussels": 2,
    "Mykonos": 4,
    "Frankfurt": 3
}

# Build the flight graph.
# Most flights are bidirectional except "from Brussels to Frankfurt" which is one-way.
graph = {city: set() for city in cities}

def add_bidirectional(a, b):
    graph[a].add(b)
    graph[b].add(a)

def add_one_way(a, b):
    graph[a].add(b)

add_bidirectional("Dublin", "Brussels")
add_bidirectional("Mykonos", "Naples")
add_bidirectional("Venice", "Istanbul")
add_bidirectional("Frankfurt", "Krakow")
add_bidirectional("Naples", "Dublin")
add_bidirectional("Krakow", "Brussels")
add_bidirectional("Naples", "Istanbul")
add_bidirectional("Naples", "Brussels")
add_bidirectional("Istanbul", "Frankfurt")
add_one_way("Brussels", "Frankfurt")  # Only from Brussels to Frankfurt.
add_bidirectional("Istanbul", "Krakow")
add_bidirectional("Istanbul", "Brussels")
add_bidirectional("Venice", "Frankfurt")
add_bidirectional("Naples", "Frankfurt")
add_bidirectional("Dublin", "Krakow")
add_bidirectional("Venice", "Brussels")
add_bidirectional("Naples", "Venice")
add_bidirectional("Istanbul", "Dublin")
add_bidirectional("Venice", "Dublin")
add_bidirectional("Dublin", "Frankfurt")

# Compute the itinerary schedule given an ordering.
# If a flight occurs on day X (from city A to city B), then the day X counts toward both A and B.
# Hence, if city[0] starts on Day 1 and lasts d0 days, its block is Day 1 to Day d0.
# The next city starts on the same day that the previous city ends.
def compute_schedule(order):
    schedule = []
    current_day = 1
    for city in order:
        d = durations[city]
        start = current_day
        end = current_day + d - 1
        schedule.append((city, start, end))
        current_day = end  # Overlap: flight day is counted for both cities.
    return schedule

# Check if a full schedule satisfies all constraints.
def check_constraints(schedule, order):
    # Overall trip must finish on Day 21.
    if schedule[-1][2] != 21:
        return False
    # Check that every consecutive flight is a direct connection.
    for i in range(len(order) - 1):
        if order[i+1] not in graph[order[i]]:
            return False
    # Fixed date constraints:
    for city, start, end in schedule:
        if city == "Dublin":
            # Must be in Dublin from Day 11 to Day 15 (exactly 5 days).
            if start != 11 or end != 15:
                return False
        if city == "Istanbul":
            # Must meet a friend in Istanbul between Day 9 and Day 11.
            # The Istanbul stay [start, end] must include at least one day in [9, 11].
            if not (start <= 11 and end >= 9):
                return False
        if city == "Frankfurt":
            # Must meet friends in Frankfurt between Day 15 and Day 17.
            if not (start <= 17 and end >= 15):
                return False
        if city == "Mykonos":
            # Must visit relatives in Mykonos between Day 1 and Day 4.
            # Require that at least one day of the Mykonos block lies in [1, 4].
            if not (start <= 4 and end >= 1):
                return False
    return True

solution_schedule = None
solution_order = None

# Given the "Mykonos" relatives constraint, we prefer to start early.
# For simplicity, we enforce that the itinerary starts with Mykonos.
for perm in itertools.permutations(cities):
    if perm[0] != "Mykonos":
        continue
    order = list(perm)
    sched = compute_schedule(order)
    if check_constraints(sched, order):
        solution_schedule = sched
        solution_order = order
        break

# Build the JSON-formatted itinerary output. Each segment indicates the day range and city.
if solution_schedule is not None:
    itinerary = []
    for city, start, end in solution_schedule:
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    output = {"itinerary": itinerary}
    print(json.dumps(output))
else:
    print(json.dumps({"itinerary": []}))