#!/usr/bin/env python3
from z3 import Solver, Int, Distinct, Implies, BoolVal, sat
import json

# Define the cities and their required durations (days)
cities = ["Valencia", "Riga", "Prague", "Mykonos", "Zurich", "Bucharest", "Nice"]
durations = {
    "Valencia": 5,
    "Riga": 5,
    "Prague": 3,
    "Mykonos": 3,
    "Zurich": 5,
    "Bucharest": 5,
    "Nice": 2
}

# Flight connections (bidirectional)
flight_graph = {
    "Valencia": ["Bucharest", "Prague", "Zurich"],
    "Riga": ["Nice", "Zurich", "Bucharest", "Prague"],
    "Prague": ["Bucharest", "Riga", "Valencia", "Zurich"],
    "Mykonos": ["Nice", "Zurich"],
    "Zurich": ["Prague", "Riga", "Bucharest", "Valencia", "Mykonos", "Nice"],
    "Bucharest": ["Prague", "Riga", "Valencia", "Zurich"],
    "Nice": ["Mykonos", "Riga", "Zurich"]
}

# Create SMT variables for each city: start day and order in the itinerary.
start_vars = {city: Int(f"start_{city}") for city in cities}
order_vars = {city: Int(f"order_{city}") for city in cities}

solver = Solver()

# Each city must have a start day between 1 and 22 and an order between 0 and 6.
for city in cities:
    solver.add(start_vars[city] >= 1, start_vars[city] <= 22)
    solver.add(order_vars[city] >= 0, order_vars[city] <= 6)

# The orders must be all different (a permutation of 0..6).
solver.add(Distinct([order_vars[city] for city in cities]))

# Ensure that each city’s visit does not extend beyond Day 22.
for city in cities:
    solver.add(start_vars[city] + durations[city] - 1 <= 22)

# If a city is the first in the itinerary (order 0), its start day must be Day 1.
for city in cities:
    solver.add(Implies(order_vars[city] == 0, start_vars[city] == 1))

# If a city is the last in the itinerary (order 6), its visit must end on Day 22.
for city in cities:
    solver.add(Implies(order_vars[city] == 6, start_vars[city] + durations[city] - 1 == 22))

# For any two distinct cities, if one immediately follows the other in the order,
# then the starting day of the successor equals the end day (overlap) of the predecessor,
# and there must be a direct flight connection between them.
for city_a in cities:
    for city_b in cities:
        if city_a == city_b:
            continue
        # When city_b immediately follows city_a, their start days must line up.
        solver.add(Implies(order_vars[city_a] + 1 == order_vars[city_b],
                           start_vars[city_b] == start_vars[city_a] + durations[city_a] - 1))
        # Enforce flight connection if they are consecutive.
        allowed_flight = (city_b in flight_graph[city_a])
        solver.add(Implies(order_vars[city_a] + 1 == order_vars[city_b],
                           BoolVal(allowed_flight)))

# Event constraints:
# The Mykonos wedding must be attended between Day 1 and Day 3.
solver.add(start_vars["Mykonos"] <= 3)

# The Prague relatives visit must occur between Day 7 and Day 9.
solver.add(start_vars["Prague"] >= 5, start_vars["Prague"] <= 9)

# Check the model.
result = solver.check()
if result == sat:
    model = solver.model()
    # Build itinerary items: sort cities by their order.
    itinerary_items = []
    sorted_itinerary = []
    for city in cities:
        o_val = model.evaluate(order_vars[city]).as_long()
        s_val = model.evaluate(start_vars[city]).as_long()
        end_val = s_val + durations[city] - 1
        sorted_itinerary.append((o_val, city, s_val, end_val))
    sorted_itinerary.sort(key=lambda x: x[0])
    
    for _, city, s_val, end_val in sorted_itinerary:
        itinerary_items.append({"day_range": f"Day {s_val}-{end_val}", "place": city})
    
    output = {"itinerary": itinerary_items}
    print(json.dumps(output, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}))