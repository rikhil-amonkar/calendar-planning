from z3 import *
import json

# Define indices for cities
# 0: Lyon (3 days)
# 1: Paris (5 days)
# 2: Riga (2 days)
# 3: Berlin (2 days)
# 4: Stockholm (3 days)
# 5: Zurich (5 days)
# 6: Nice (2 days)
# 7: Seville (3 days)
# 8: Milan (3 days)
# 9: Naples (4 days)
cities = ["Lyon", "Paris", "Riga", "Berlin", "Stockholm", "Zurich", "Nice", "Seville", "Milan", "Naples"]
durations = [3, 5, 2, 2, 3, 5, 2, 3, 3, 4]

# Allowed direct flights (neighbors) for each city (using indices)
allowed_neighbors = {
    0: [1, 6],             # Lyon connects to Paris and Nice
    1: [0, 2, 3, 4, 5, 6, 7, 8, 9],  # Paris connects to everyone except itself (from given flights)
    2: [1, 3, 4, 5, 6, 8],  # Riga connects to Paris, Berlin, Stockholm, Zurich, Nice, Milan
    3: [1, 2, 4, 6, 8, 9],  # Berlin connects to Paris, Riga, Stockholm, Nice, Milan, Naples
    4: [1, 2, 3, 5, 6, 8],  # Stockholm connects to Paris, Riga, Berlin, Zurich, Nice, Milan
    5: [1, 2, 4, 6, 8, 9],  # Zurich connects to Paris, Riga, Stockholm, Nice, Milan, Naples
    6: [0, 1, 2, 3, 4, 5, 9],  # Nice connects to Lyon, Paris, Riga, Berlin, Stockholm, Zurich, Naples
    7: [1],                # Seville only connects to Paris
    8: [1, 2, 3, 4, 5, 9],  # Milan connects to Paris, Riga, Berlin, Stockholm, Zurich, Naples
    9: [1, 3, 5, 6, 8]     # Naples connects to Paris, Berlin, Zurich, Nice, Milan
}

# Create the solver instance
solver = Solver()

# Create variables:
# order[i] represents the city index visited in position i (0-indexed positions for 10 cities)
order = [Int(f"order_{i}") for i in range(10)]
# T[i] represents the starting day for the segment corresponding to the city at position i.
T = [Int(f"T_{i}") for i in range(10)]

# Domain constraints for order (each city index must be between 0 and 9)
for i in range(10):
    solver.add(order[i] >= 0, order[i] < 10)

# All cities must be visited exactly once.
solver.add(Distinct(order))

# Define a helper function to get the duration of a city given a Z3 expression representing its index.
def get_duration(city_expr):
    return If(city_expr == 0, durations[0],
           If(city_expr == 1, durations[1],
           If(city_expr == 2, durations[2],
           If(city_expr == 3, durations[3],
           If(city_expr == 4, durations[4],
           If(city_expr == 5, durations[5],
           If(city_expr == 6, durations[6],
           If(city_expr == 7, durations[7],
           If(city_expr == 8, durations[8],
              durations[9]))))))))

# The trip is exactly 23 days.
# We have an overlap day when flying between cities.
# The structure: The first city is visited from day T_0 to T_0 + duration - 1.
# For i>=1, T[i] = T[i-1] + (duration(previous) - 1)
solver.add(T[0] == 1)
for i in range(9):
    solver.add(T[i+1] == T[i] + (get_duration(order[i]) - 1))
# Last city's end day must equal 23.
solver.add(T[9] + get_duration(order[9]) - 1 == 23)

# Special event constraints:
# Wedding in Berlin: Berlin (index 3) must be visited such that its interval includes day 1 or day 2.
# Since the interval for the city at position i is [T[i], T[i] + (duration - 1)],
# we require that if Berlin is visited then T[i] <= 2.
for i in range(10):
    solver.add(Implies(order[i] == 3, T[i] <= 2))

# Annual show in Stockholm between day 20 and day 22:
# Stockholm (index 4) has a duration of 3 days, so it must exactly cover days 20-22.
for i in range(10):
    solver.add(Implies(order[i] == 4, T[i] == 20))

# Workshop in Nice between day 12 and day 13:
# Nice (index 6) with duration 2 must include either day 12 or 13.
# Its interval is [T[i], T[i]+1], so we require T[i] == 11, or T[i] == 12, or T[i] == 13.
for i in range(10):
    solver.add(Implies(order[i] == 6, Or(T[i] == 11, T[i] == 12, T[i] == 13)))

# Flight connectivity constraints: consecutive cities in the itinerary must have a direct flight.
for i in range(9):
    # For each possible city at position i, enforce that the city at position i+1 is in its allowed neighbors.
    constraints = []
    for city in range(10):
        if city in allowed_neighbors:
            neighbors = allowed_neighbors[city]
            # Build Or condition for neighbors of 'city'
            neighbor_cond = Or([order[i+1] == nb for nb in neighbors])
            constraints.append(Implies(order[i] == city, neighbor_cond))
    solver.add(And(constraints))

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(10):
        city_index = model.evaluate(order[i]).as_long()
        start_day = model.evaluate(T[i]).as_long()
        duration_val = durations[city_index]
        end_day = start_day + duration_val - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": cities[city_index]
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))