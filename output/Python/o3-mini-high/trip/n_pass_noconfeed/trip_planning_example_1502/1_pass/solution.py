import json

# Data: cities with required durations (in days)
durations = {
    "Santorini": 3,
    "Valencia": 4,
    "Madrid": 2,
    "Seville": 2,
    "Bucharest": 3,
    "Vienna": 4,
    "Riga": 4,
    "Tallinn": 5,
    "Krakow": 5,
    "Frankfurt": 4
}

# Event constraints:
# For a city with a scheduled event, the block (from start day S to S + duration - 1)
# must include the given event day(s). For simplicity, we enforce:
# - Madrid: must start exactly on day 6 so that its 2-day span is Day 6-7 (annual show)
# - Vienna: wedding must be attended between day 3 and day 6; we require the Vienna block to start no later than day 6.
# - Krakow: friends meeting must occur between day 11 and day 15; so the Krakow block (5 days) must overlap [11,15].
# - Riga: conference requires presence on day 20 and day 23; force Riga's block to start at day 20.
# - Tallinn: workshop happens between day 23 and day 27; force Tallinn's block to start at day 23.
event_constraints = {
    "Madrid": lambda s, d: s == 6,
    "Vienna": lambda s, d: s <= 6,  # block covers s ... s+3 so if s<=6, then day6 is included in some cases (wedding)
    "Krakow": lambda s, d: s <= 15 and (s + d - 1) >= 11,
    "Riga": lambda s, d: s == 20,
    "Tallinn": lambda s, d: s == 23
}

# Allowed flight connections.
# Most connections are bidirectional except for the explicitly directed edge from Riga to Tallinn.
allowed_flights = {
    "Vienna": set(["Bucharest", "Seville", "Valencia", "Madrid", "Santorini", "Krakow", "Frankfurt", "Riga"]),
    "Bucharest": set(["Vienna", "Riga", "Santorini", "Valencia", "Madrid", "Frankfurt"]),
    "Santorini": set(["Madrid", "Bucharest", "Vienna"]),
    "Madrid": set(["Santorini", "Valencia", "Seville", "Bucharest", "Frankfurt", "Vienna"]),
    "Seville": set(["Valencia", "Madrid", "Vienna"]),
    "Valencia": set(["Seville", "Madrid", "Bucharest", "Krakow", "Frankfurt", "Vienna"]),
    "Krakow": set(["Valencia", "Frankfurt", "Vienna"]),
    "Frankfurt": set(["Valencia", "Bucharest", "Krakow", "Tallinn", "Riga", "Madrid", "Vienna"]),
    "Riga": set(["Bucharest", "Vienna", "Frankfurt"]),
    "Tallinn": set(["Frankfurt"])  # Bidirectional edge "Frankfurt and Tallinn" gives Tallinn->Frankfurt.
}

# Add the bidirectional edges that might have been omitted: 
# Many pairs are symmetric so we update both sides.
def add_bidirectional(a, b):
    allowed_flights.setdefault(a, set()).add(b)
    allowed_flights.setdefault(b, set()).add(a)

# Provided pairs (if not already in the dictionary)
pairs = [
    ("Vienna", "Bucharest"),
    ("Santorini", "Madrid"),
    ("Seville", "Valencia"),
    ("Vienna", "Seville"),
    ("Madrid", "Valencia"),
    ("Bucharest", "Riga"),
    ("Valencia", "Bucharest"),
    ("Santorini", "Bucharest"),
    ("Vienna", "Valencia"),
    ("Vienna", "Madrid"),
    ("Valencia", "Krakow"),
    ("Valencia", "Frankfurt"),
    ("Krakow", "Frankfurt"),
    # Riga -> Tallinn is one directional, so do not add reverse.
    ("Vienna", "Krakow"),
    ("Vienna", "Frankfurt"),
    ("Madrid", "Seville"),
    ("Santorini", "Vienna"),
    ("Vienna", "Riga"),
    ("Frankfurt", "Tallinn"),
    ("Frankfurt", "Bucharest"),
    ("Madrid", "Bucharest"),
    ("Frankfurt", "Riga"),
    ("Madrid", "Frankfurt")
]
for a, b in pairs:
    # For the Riga->Tallinn edge, we have special handling below.
    if (a, b) == ("Riga", "Tallinn"):
        allowed_flights.setdefault("Riga", set()).add("Tallinn")
    elif (b, a) == ("Riga", "Tallinn"):
        allowed_flights.setdefault("Riga", set()).add("Tallinn")
    else:
        add_bidirectional(a, b)

# Ensure Riga->Tallinn edge is present as directed edge.
allowed_flights.setdefault("Riga", set()).add("Tallinn")
# (Do not add the reverse direction for Riga-Tallinn if not provided.)

# List of all cities. The order here is arbitrary; the backtracking search will decide the itinerary.
cities = ["Santorini", "Valencia", "Madrid", "Seville", "Bucharest", "Vienna", "Riga", "Tallinn", "Krakow", "Frankfurt"]

# Backtracking solver.
def backtrack(order, used, current_start):
    if len(order) == len(cities):
        return order
    
    # Try each city not in the current order.
    for city in cities:
        if city in used:
            continue
        # If not the first city, check if there is a direct flight from the previous city.
        if order:
            prev_city = order[-1]
            # Check flight connection (if the candidate is reachable from previous city)
            if city not in allowed_flights.get(prev_city, set()):
                continue
        # Check event constraint if it exists for this city.
        d = durations[city]
        if city in event_constraints:
            if not event_constraints[city](current_start, d):
                continue
        # Choose city and update the next start day.
        new_start = current_start + d - 1  # Flight day is double-counted.
        order.append(city)
        used.add(city)
        result = backtrack(order, used, new_start)
        if result is not None:
            return result
        order.pop()
        used.remove(city)
    return None

def compute_itinerary(order):
    itinerary = []
    start_day = 1
    for city in order:
        d = durations[city]
        end_day = start_day + d - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        start_day = start_day + d - 1
    return itinerary

if __name__ == "__main__":
    solution_order = backtrack([], set(), 1)
    if solution_order is None:
        output = {"itinerary": []}
    else:
        itinerary = compute_itinerary(solution_order)
        output = {"itinerary": itinerary}
    print(json.dumps(output))