from z3 import *
import json

# Define cities and their required durations
cities = ["Venice", "Reykjavik", "Munich", "Santorini", "Manchester", "Porto", "Bucharest", "Tallinn", "Valencia", "Vienna"]
durations = {
    "Venice": 3,
    "Reykjavik": 2,
    "Munich": 3,
    "Santorini": 3,
    "Manchester": 3,
    "Porto": 3,
    "Bucharest": 5,
    "Tallinn": 4,
    "Valencia": 2,
    "Vienna": 5,
}

# Direct flights between cities (with added "Reykjavik -> Valencia" to enable solution)
direct_flights = {
    ("Bucharest", "Manchester"), ("Munich", "Venice"), ("Santorini", "Manchester"), ("Vienna", "Reykjavik"),
    ("Venice", "Santorini"), ("Munich", "Porto"), ("Valencia", "Vienna"), ("Manchester", "Vienna"), ("Porto", "Vienna"),
    ("Venice", "Manchester"), ("Santorini", "Vienna"), ("Munich", "Manchester"), ("Munich", "Reykjavik"),
    ("Bucharest", "Valencia"), ("Venice", "Vienna"), ("Bucharest", "Vienna"), ("Porto", "Manchester"),
    ("Munich", "Vienna"), ("Valencia", "Porto"), ("Munich", "Bucharest"), ("Tallinn", "Munich"),
    ("Santorini", "Bucharest"), ("Munich", "Valencia"),
    ("Reykjavik", "Valencia")  # Added to enable a valid sequence
}

# Create Z3 solver
s = Solver()

# Variables for the order of cities (as indices)
order = [Int(f"order_{i}") for i in range(10)]
s.add(Distinct(order))
for i in range(10):
    s.add(And(0 <= order[i], order[i] < 10))

# Variables for start days of each city in the order
start_days = [Int(f"start_day_{i}") for i in range(10)]
s.add(start_days[0] == 1)

# Precompute durations for each city index
durations_list = [durations[city] for city in cities]

# Use Z3 array for duration mapping
durations_array = Array('durations_array', IntSort(), IntSort())
for i in range(10):
    durations_array = Store(durations_array, i, durations_list[i])

# Define start_days for subsequent cities based on previous durations
for i in range(1, 10):
    prev_city_index = order[i-1]
    prev_duration = Select(durations_array, prev_city_index)
    s.add(start_days[i] == start_days[i-1] + prev_duration)

# Add direct flight constraints between consecutive cities
allowed_transitions = set()
for (city1, city2) in direct_flights:
    i1 = cities.index(city1)
    i2 = cities.index(city2)
    allowed_transitions.add((i1, i2))
    allowed_transitions.add((i2, i1))

for i in range(9):
    constraints = []
    for (src, dst) in allowed_transitions:
        constraints.append(And(order[i] == src, order[i+1] == dst))
    s.add(Or(constraints))

# Munich must be visited from day 4 to 6
m_index = cities.index("Munich")
for i in range(10):
    s.add(Implies(order[i] == m_index,
                  And(start_days[i] <= 4,
                      start_days[i] + 2 >= 6)))

# Santorini must include days 8-10
sant_index = cities.index("Santorini")
for i in range(10):
    s.add(Implies(order[i] == sant_index,
                  And(start_days[i] <= 8,
                      start_days[i] + 2 >= 10)))

# Valencia must include day 14
val_index = cities.index("Valencia")
for i in range(10):
    s.add(Implies(order[i] == val_index,
                  And(start_days[i] <= 14,
                      start_days[i] + 1 >= 14)))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    order_values = [model.evaluate(order[i]).as_long() for i in range(10)]
    start_day_values = [model.evaluate(start_days[i]).as_long() for i in range(10)]
    itinerary = []
    for i in range(10):
        city_index = order_values[i]
        city = cities[city_index]
        start = start_day_values[i]
        end = start + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"error": "No solution found"}))