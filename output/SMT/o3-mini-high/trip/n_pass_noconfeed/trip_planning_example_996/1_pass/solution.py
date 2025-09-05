from z3 import Solver, Int, If, Distinct, And, Or, Implies, BoolVal
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

# For every city, ensure that its visit does not extend beyond day 22.
for city in cities:
    solver.add(start_vars[city] + durations[city] - 1 <= 22)

# If a city is the first in the itinerary (order 0), its start day must be Day 1.
for city in cities:
    solver.add(Implies(order_vars[city] == 0, start_vars[city] == 1))

# If a city is the last in the itinerary (order 6), its visit must end on Day 22.
for city in cities:
    solver.add(Implies(order_vars[city] == 6, start_vars[city] + durations[city] - 1 == 22))

# For any two distinct cities, if one immediately follows the other in the order,
# then the starting day of the successor equals the end day (with overlap) of the predecessor.
# Also, a direct flight connection must exist between them.
for city_a in cities:
    for city_b in cities:
        if city_a == city_b:
            continue
        # If city_b immediately follows city_a:
        solver.add(Implies(order_vars[city_a] + 1 == order_vars[city_b],
                           start_vars[city_b] == start_vars[city_a] + durations[city_a] - 1))
        # Enforce flight connection: if city_b is immediately after city_a, there must be a direct flight.
        # (Since flight_graph is fixed, we encode the allowed connection as a Boolean constant.)
        allowed_flight = (city_b in flight_graph[city_a])
        solver.add(Implies(order_vars[city_a] + 1 == order_vars[city_b],
                           BoolVal(allowed_flight)))

# Event constraints:
# Mykonos wedding must be attended on a day between Day 1 and Day 3.
# Since Mykonos is visited for 3 days starting at start_Mykonos, at least one of those days must be in [1,3].
# It is sufficient to require that the visit starts on or before Day 3.
solver.add(start_vars["Mykonos"] <= 3)

# Prague relatives visit must occur between Day 7 and Day 9.
# Prague is visited for 3 days, so for an overlap with [7,9] we require:
# start_Prague <= 9 and start_Prague + 3 - 1 (i.e. end day) >= 7, which is equivalent to start_Prague >= 5.
solver.add(start_vars["Prague"] <= 9, start_vars["Prague"] >= 5)

# At this point the SMT model fully encodes our itinerary:
# The overall itinerary will cover exactly 22 days because:
# Sum(durations) - (number of transitions) = 5+5+3+3+5+5+2 - 6 = 28 - 6 = 22.

if solver.check() == "sat":
    model = solver.model()
    # Build itinerary items: sort cities by their order in the itinerary.
    itinerary = []
    # Create a list of tuples (order, city, start, end)
    sorted_itinerary = []
    for city in cities:
        o_val = model.evaluate(order_vars[city]).as_long()
        s_val = model.evaluate(start_vars[city]).as_long()
        end_val = s_val + durations[city] - 1
        sorted_itinerary.append((o_val, city, s_val, end_val))
    sorted_itinerary.sort(key=lambda x: x[0])
    
    # Build the list in the specified JSON format.
    itinerary_list = []
    for _, city, s_val, end_val in sorted_itinerary:
        itinerary_list.append({"day_range": f"Day {s_val}-{end_val}", "place": city})
    
    output = {"itinerary": itinerary_list}
    print(json.dumps(output))
else:
    print(json.dumps({"error": "No valid itinerary found"}))