import json
from z3 import *

# Define the cities
cities = {
    "Lisbon": 0,
    "Dubrovnik": 1,
    "Copenhagen": 2,
    "Prague": 3,
    "Tallinn": 4,
    "Stockholm": 5,
    "Split": 6,
    "Lyon": 7
}

# Inverse mapping for output
city_names = {v: k for k, v in cities.items()}

# Direct flights: adjacency list
direct_flights = {
    0: [2, 7, 5, 3],  # Lisbon -> Copenhagen, Lyon, Stockholm, Prague
    1: [5, 2],         # Dubrovnik -> Stockholm, Copenhagen
    2: [5, 6, 0, 3, 4, 1],  # Copenhagen -> Stockholm, Split, Lisbon, Prague, Tallinn, Dubrovnik
    3: [5, 7, 0, 2, 6, 4],   # Prague -> Stockholm, Lyon, Lisbon, Copenhagen, Split, Tallinn
    4: [5, 2, 3],      # Tallinn -> Stockholm, Copenhagen, Prague
    5: [0, 2, 3, 4, 6, 1],  # Stockholm -> Lisbon, Copenhagen, Prague, Tallinn, Split, Dubrovnik
    6: [2, 5, 7, 3],   # Split -> Copenhagen, Stockholm, Lyon, Prague
    7: [0, 3, 6]       # Lyon -> Lisbon, Prague, Split
}

# Total days
days = 19

# Create Z3 variables: day[i] is the city on day i+1 (days are 1-based)
day_vars = [Int(f"day_{i}") for i in range(days)]

solver = Solver()

# Each day variable must be one of the cities
for d in day_vars:
    solver.add(Or([d == c for c in cities.values()]))

# Duration constraints
# Lisbon: 2 days
solver.add(Sum([If(d == cities["Lisbon"], 1, 0) for d in day_vars]) == 2)
# Dubrovnik: 5 days
solver.add(Sum([If(d == cities["Dubrovnik"], 1, 0) for d in day_vars]) == 5)
# Copenhagen: 5 days
solver.add(Sum([If(d == cities["Copenhagen"], 1, 0) for d in day_vars]) == 5)
# Prague: 3 days
solver.add(Sum([If(d == cities["Prague"], 1, 0) for d in day_vars]) == 3)
# Tallinn: 2 days
solver.add(Sum([If(d == cities["Tallinn"], 1, 0) for d in day_vars]) == 2)
# Stockholm: 4 days
solver.add(Sum([If(d == cities["Stockholm"], 1, 0) for d in day_vars]) == 4)
# Split: 3 days
solver.add(Sum([If(d == cities["Split"], 1, 0) for d in day_vars]) == 3)
# Lyon: 2 days
solver.add(Sum([If(d == cities["Lyon"], 1, 0) for d in day_vars]) == 2)

# Event constraints
# Workshop in Lisbon between day 4 and 5 (i.e., day 4 or 5 is Lisbon)
solver.add(Or(day_vars[3] == cities["Lisbon"], day_vars[4] == cities["Lisbon"]))
# Meet friend in Tallinn between day 1 and 2 (day 1 or 2 is Tallinn)
solver.add(Or(day_vars[0] == cities["Tallinn"], day_vars[1] == cities["Tallinn"]))
# Wedding in Stockholm between day 13 and 16 (day 13, 14, 15, or 16 is Stockholm)
solver.add(Or([day_vars[i] == cities["Stockholm"] for i in range(12, 16)]))
# Annual show in Lyon from day 18 to 19 (day 18 and 19 are Lyon)
solver.add(day_vars[17] == cities["Lyon"])
solver.add(day_vars[18] == cities["Lyon"])

# Flight constraints: consecutive days must be either same city or connected by direct flight
for i in range(days - 1):
    current_city = day_vars[i]
    next_city = day_vars[i + 1]
    solver.add(Or([
        And(current_city == c,
            Or([next_city == d for d in direct_flights[c]] + [next_city == c]))
        for c in direct_flights.keys()
    ]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(days):
        city_code = model.evaluate(day_vars[i]).as_long()
        itinerary.append({"day": i + 1, "place": city_names[city_code]})
    
    # Prepare the output
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No valid itinerary found.")