import itertools
import json

# Input variables: cities, durations, flight connections, and event constraints.
cities = ["Berlin", "Paris", "Lyon", "Riga", "Stockholm", "Zurich", "Nice", "Seville", "Milan", "Naples"]
durations = {
    "Berlin": 2,
    "Paris": 5,
    "Lyon": 3,
    "Riga": 2,
    "Stockholm": 3,
    "Zurich": 5,
    "Nice": 2,
    "Seville": 3,
    "Milan": 3,
    "Naples": 4
}

# Event constraints (each event forces the city to be scheduled at a specific time window)
# Note: With the overlapping flight rule and total trip days = sum(durations) - (#flights) 
# the start day for a city at position i is fixed by the ordering:
#    start_day[0] = 1 and for i >= 1, start_day[i] = finish_day[i-1] where finish_day[i-1] = (sum of durations up to city i-1) - (i-1)
# Wedding in Berlin must happen between Day 1 and Day 2 -> Berlin must be the first city.
# Workshop in Nice must happen on day 12-13 -> Nice's segment must start exactly on Day 12.
# Annual show in Stockholm must be attended from Day 20 to Day 22 -> Stockholm's segment must start exactly on Day 20.
event_constraints = {
    "Nice": 12,
    "Stockholm": 20
}
total_days = sum(durations.values()) - (len(cities) - 1)  # should equal 23

# Define the list of direct flight connections (bidirectional)
flight_pairs = [
    ("Paris", "Stockholm"),
    ("Seville", "Paris"),
    ("Naples", "Zurich"),
    ("Nice", "Riga"),
    ("Berlin", "Milan"),
    ("Paris", "Zurich"),
    ("Paris", "Nice"),
    ("Milan", "Paris"),
    ("Milan", "Riga"),
    ("Paris", "Lyon"),
    ("Milan", "Naples"),
    ("Paris", "Riga"),
    ("Berlin", "Stockholm"),
    ("Stockholm", "Riga"),
    ("Nice", "Zurich"),
    ("Milan", "Zurich"),
    ("Lyon", "Nice"),
    ("Zurich", "Stockholm"),
    ("Zurich", "Riga"),
    ("Berlin", "Naples"),
    ("Milan", "Stockholm"),
    ("Berlin", "Zurich"),
    ("Milan", "Seville"),
    ("Paris", "Naples"),
    ("Berlin", "Riga"),
    ("Nice", "Stockholm"),
    ("Berlin", "Paris"),
    ("Nice", "Naples"),
    ("Berlin", "Nice")
]

# Build an adjacency dictionary for flights (bidirectional)
flights = {city: set() for city in cities}
for a, b in flight_pairs:
    flights[a].add(b)
    flights[b].add(a)

# Helper function to compute the schedule given an ordering.
def compute_schedule(order):
    schedule = []
    current_day = 1
    for city in order:
        start_day = current_day
        finish_day = start_day + durations[city] - 1
        schedule.append((city, start_day, finish_day))
        # If we fly on the same day as the end of stay, that day counts for both cities.
        # So next city's start day is the same as today's finish day.
        current_day = finish_day
    return schedule

# Check if the flight leg between two cities exists (direct flight)
def valid_flight(a, b):
    return b in flights[a]

# The first city must be Berlin (wedding constraint)
fixed_start = "Berlin"
remaining_cities = [city for city in cities if city != fixed_start]

valid_itinerary = None

# Search for a permutation of the remaining cities that meets all constraints.
for perm in itertools.permutations(remaining_cities):
    route = [fixed_start] + list(perm)
    
    # Check flight connectivity for each consecutive leg.
    leg_ok = True
    for i in range(len(route) - 1):
        if not valid_flight(route[i], route[i+1]):
            leg_ok = False
            break
    if not leg_ok:
        continue

    sched = compute_schedule(route)
    
    # Total days check
    if sched[-1][2] != total_days:
        continue

    # Check event constraints:
    meets_events = True
    for city, required_start in event_constraints.items():
        # Find the scheduled segment for the city
        seg = next((seg for seg in sched if seg[0] == city), None)
        if seg is None or seg[1] != required_start:
            meets_events = False
            break
    if not meets_events:
        continue

    # If all constraints satisfied, use this itinerary.
    valid_itinerary = sched
    break

# Prepare output in the JSON structure.
if valid_itinerary is not None:
    itinerary_output = []
    for city, start, finish in valid_itinerary:
        # Format day range as "Day X-Y"
        itinerary_output.append({
            "day_range": f"Day {start}-{finish}",
            "place": city
        })
    output = {"itinerary": itinerary_output}
else:
    output = {"itinerary": []}

print(json.dumps(output))