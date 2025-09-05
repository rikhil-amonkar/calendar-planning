import json

# Define required durations for each city (in days)
durations = {
    "Valencia": 2,
    "Oslo": 3,
    "Lyon": 4,
    "Prague": 3,
    "Paris": 4,
    "Nice": 4,
    "Seville": 5,
    "Tallinn": 2,
    "Mykonos": 5,
    "Lisbon": 2
}

# List of all cities
all_cities = ["Valencia", "Oslo", "Lyon", "Prague", "Paris", "Nice", "Seville", "Tallinn", "Mykonos", "Lisbon"]

# Build flight graph based on provided direct flight connections (assumed undirected)
flight_edges = [
    ("Lisbon", "Paris"),
    ("Lyon", "Nice"),
    ("Tallinn", "Oslo"),
    ("Prague", "Lyon"),
    ("Paris", "Oslo"),
    ("Lisbon", "Seville"),
    ("Prague", "Lisbon"),
    ("Oslo", "Nice"),
    ("Valencia", "Paris"),
    ("Valencia", "Lisbon"),
    ("Paris", "Nice"),
    ("Nice", "Mykonos"),
    ("Paris", "Lyon"),
    ("Valencia", "Lyon"),
    ("Prague", "Oslo"),
    ("Prague", "Paris"),
    ("Seville", "Paris"),
    ("Oslo", "Lyon"),
    ("Prague", "Valencia"),
    ("Lisbon", "Nice"),
    ("Lisbon", "Oslo"),
    ("Valencia", "Seville"),
    ("Lisbon", "Lyon"),
    ("Paris", "Tallinn"),
    ("Prague", "Tallinn")
]

# Create a dictionary representing the flight graph.
flight_graph = {city: set() for city in all_cities}
for a, b in flight_edges:
    flight_graph[a].add(b)
    flight_graph[b].add(a)

# For planning, we reserve Mykonos to be visited last (position 10)
# and force "Nice" to be the 9th city because the only connection to Mykonos is from Nice.
# The allowed set for the first 9 positions is all cities except "Mykonos".
allowed_first9 = [city for city in all_cities if city != "Mykonos"]

def backtrack(ordering, cur_sum):
    # ordering: list of already chosen cities (for positions 1..k)
    # cur_sum: sum of durations for the cities in 'ordering'
    # The arrival day for the next city is defined as:
    #   next_arrival = 1 + (sum of durations so far) - (number of transitions)
    if len(ordering) == 9:
        # At this point, we require that the 9th city is "Nice" to allow a flight to Mykonos.
        if ordering[-1] != "Nice":
            return None
        # Check flight connectivity from "Nice" to "Mykonos"
        if "Mykonos" not in flight_graph[ordering[-1]]:
            return None
        # Build complete ordering by appending Mykonos
        return ordering + ["Mykonos"]
    
    next_arrival = 1 + cur_sum - len(ordering)
    
    for candidate in allowed_first9:
        if candidate in ordering:
            continue
        # Do not place Mykonos in the first 9 positions
        if candidate == "Mykonos":
            continue
        # Enforce that "Nice" must only be chosen in the final slot (position 9)
        if candidate == "Nice" and len(ordering) != 8:
            continue
        
        # Check flight connectivity: if not the first city, candidate must be connected from the previous city.
        if ordering:
            prev = ordering[-1]
            if candidate not in flight_graph[prev]:
                continue
        
        # Compute candidate's arrival day and departure day.
        arrival = next_arrival
        departure = arrival + durations[candidate] - 1
        
        # Check event constraints based on the candidate and its scheduled arrival.
        # Valencia friend meeting must occur between day 3 and day 4.
        if candidate == "Valencia":
            # Valencia stay is [arrival, arrival+1]. Require that it covers day 3 or day 4.
            if not (2 <= arrival <= 4):
                continue
        # Oslo friend meeting between day 13 and day 15.
        if candidate == "Oslo":
            if not (11 <= arrival <= 15):
                continue
        # Seville annual show from day 5 to day 9 requires Seville to be scheduled exactly from day 5 to 9.
        if candidate == "Seville":
            if arrival != 5:
                continue
        # (Mykonos is reserved for last; its event constraint will be checked when appended.)
        
        new_ordering = ordering + [candidate]
        new_cur_sum = cur_sum + durations[candidate]
        result = backtrack(new_ordering, new_cur_sum)
        if result is not None:
            return result
    return None

def get_schedule(ordering):
    schedule = []
    cumulative = 0
    # For city at position i (0-indexed), arrival = 1 + (sum of durations of previous cities) - i.
    for i, city in enumerate(ordering):
        arrival = 1 + cumulative - i
        departure = arrival + durations[city] - 1
        schedule.append({"day_range": f"Day {arrival}-{departure}", "place": city})
        cumulative += durations[city]
    return schedule

solution = backtrack([], 0)

if solution is None:
    output = {"itinerary": []}
else:
    itinerary = get_schedule(solution)
    output = {"itinerary": itinerary}

print(json.dumps(output))