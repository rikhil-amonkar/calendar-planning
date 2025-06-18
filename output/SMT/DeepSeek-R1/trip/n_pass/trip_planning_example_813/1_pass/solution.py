from z3 import *

# Cities and their required days
requirements = {
    "Seville": 5,
    "Vilnius": 3,
    "Santorini": 2,
    "London": 2,
    "Stuttgart": 3,
    "Dublin": 3,
    "Frankfurt": 5
}

# Direct flights
direct_flights = [
    "Frankfurt and Dublin",
    "Frankfurt and London",
    "London and Dublin",
    "Vilnius and Frankfurt",
    "Frankfurt and Stuttgart",
    "Dublin and Seville",
    "London and Santorini",
    "Stuttgart and London",
    "Santorini and Dublin"
]

# Map city names to integer IDs
city_ids = {
    "Seville": 0,
    "Vilnius": 1,
    "Santorini": 2,
    "London": 3,
    "Stuttgart": 4,
    "Dublin": 5,
    "Frankfurt": 6
}
ids_to_city = {v: k for k, v in city_ids.items()}

# Create a set of direct flight pairs (both directions)
direct_flights_ids = set()
for flight in direct_flights:
    parts = flight.split(" and ")
    c1, c2 = parts[0], parts[1]
    id1 = city_ids[c1]
    id2 = city_ids[c2]
    direct_flights_ids.add((id1, id2))
    direct_flights_ids.add((id2, id1))

# Initialize Z3 solver
solver = Solver()

# Define start and end day variables for each city
start = [Int(f'start_{i}') for i in range(7)]
end = [Int(f'end_{i}') for i in range(7)]

# Fixed constraints for London, Stuttgart, and Frankfurt
solver.add(start[city_ids["London"]] == 9)
solver.add(end[city_ids["London"]] == 10)
solver.add(start[city_ids["Stuttgart"]] == 7)
solver.add(end[city_ids["Stuttgart"]] == 9)
solver.add(start[city_ids["Frankfurt"]] == 3)
solver.add(end[city_ids["Frankfurt"]] == 7)

# End day constraints for other cities
for city, days in requirements.items():
    cid = city_ids[city]
    if city not in ["London", "Stuttgart", "Frankfurt"]:
        solver.add(end[cid] == start[cid] + days - 1)

# Order of cities (permutation)
order = [Int(f'order_{i}') for i in range(7)]
for i in range(7):
    solver.add(order[i] >= 0, order[i] <= 6)
solver.add(Distinct(order))

# Position of Frankfurt, Stuttgart, and London in the order
i = Int('i')
solver.add(i >= 1, i <= 4)
solver.add(order[i] == city_ids["Frankfurt"])
solver.add(order[i+1] == city_ids["Stuttgart"])
solver.add(order[i+2] == city_ids["London"])

# Other cities in the order
other_city_ids = [city_ids[c] for c in ["Seville", "Vilnius", "Santorini", "Dublin"]]
for pos in range(7):
    if pos == i or pos == i+1 or pos == i+2:
        continue
    solver.add(Or([order[pos] == id for id in other_city_ids]))

# Consecutive city constraints
for idx in range(6):
    city1 = order[idx]
    city2 = order[idx+1]
    solver.add(end[city1] == start[city2])
    # Check for direct flight
    options = []
    for (id1, id2) in direct_flights_ids:
        options.append(And(city1 == id1, city2 == id2))
    solver.add(Or(options))

# First city starts on day 1, last city ends on day 17
solver.add(start[order[0]] == 1)
solver.add(end[order[6]] == 17)

# Start and end days must be within 1 to 17
for j in range(7):
    solver.add(start[j] >= 1)
    solver.add(start[j] <= 17)
    solver.add(end[j] >= 1)
    solver.add(end[j] <= 17)

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    # Extract the order
    order_vals = [model.evaluate(order[j]).as_long() for j in range(7)]
    # Extract start and end days
    start_vals = [model.evaluate(start[j]).as_long() for j in range(7)]
    end_vals = [model.evaluate(end[j]).as_long() for j in range(7)]
    
    # Generate itinerary
    itinerary = []
    for idx in range(7):
        city_id = order_vals[idx]
        city_name = ids_to_city[city_id]
        s = start_vals[city_id]
        e = end_vals[city_id]
        # Add the consecutive stay
        if s == e:
            range_str = f"Day {s}"
        else:
            range_str = f"Day {s}-{e}"
        itinerary.append({"day_range": range_str, "place": city_name})
        # If not the last city, add departure and next city's arrival
        if idx < 6:
            next_city_id = order_vals[idx+1]
            next_city_name = ids_to_city[next_city_id]
            itinerary.append({"day_range": f"Day {e}", "place": city_name})
            itinerary.append({"day_range": f"Day {e}", "place": next_city_name})
    
    # Output as JSON
    import json
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")