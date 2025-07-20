import json
from z3 import *

# Define the cities and their required days
cities = {
    "Oslo": 5,
    "Stuttgart": 5,
    "Reykjavik": 2,
    "Split": 3,
    "Geneva": 2,
    "Porto": 3,
    "Tallinn": 5,
    "Stockholm": 3
}

# Direct flights: key is the source, value is the list of destinations
direct_flights = {
    "Reykjavik": ["Stuttgart", "Stockholm", "Tallinn", "Oslo"],
    "Stockholm": ["Oslo", "Stuttgart", "Split", "Geneva"],
    "Stuttgart": ["Porto", "Stockholm", "Split"],
    "Oslo": ["Split", "Geneva", "Porto", "Stockholm", "Tallinn"],
    "Split": ["Stuttgart", "Geneva", "Stockholm"],
    "Geneva": ["Porto", "Split", "Stockholm"],
    "Porto": [],  # No outgoing flights needed as per the problem statement
    "Tallinn": ["Oslo"]
}

# Create a reverse mapping for flights (bidirectional for ease)
# But according to the problem, flights are direct as listed, so we'll use the given structure.

# Initialize Z3 variables for each day (1..21)
days = 21
day_vars = [Int(f"day_{i}") for i in range(1, days + 1)]

solver = Solver()

# Define city encodings (integers)
city_ids = {city: idx for idx, city in enumerate(cities.keys())}
id_to_city = {idx: city for city, idx in city_ids.items()}

# Constraint: Each day variable must be one of the city IDs
for day in day_vars:
    solver.add(Or([day == city_ids[city] for city in cities]))

# Fixed constraints:
# Day 1 and 2 in Reykjavik
solver.add(day_vars[0] == city_ids["Reykjavik"])
solver.add(day_vars[1] == city_ids["Reykjavik"])

# Workshop in Porto between day 19-21 (indices 18-20)
solver.add(day_vars[18] == city_ids["Porto"])
solver.add(day_vars[19] == city_ids["Porto"])
solver.add(day_vars[20] == city_ids["Porto"])

# Meet friend in Stockholm between day 2 and 4 (indices 1-3, but day 2 is index 1)
# So Stockholm must appear on at least one of days 2, 3, or 4 (indices 1, 2, 3)
solver.add(Or([day_vars[i] == city_ids["Stockholm"] for i in [1, 2, 3]]))

# Flight transitions: if day i and i+1 are different, then there must be a direct flight
for i in range(days - 1):
    current_day = day_vars[i]
    next_day = day_vars[i + 1]
    # If the cities are different, check flight exists
    solver.add(Implies(current_day != next_day, 
                      Or([And(current_day == city_ids[src], next_day == city_ids[dst]) 
                          for src in direct_flights 
                          for dst in direct_flights[src]])))

# Count the number of days per city and match the required days
for city in cities:
    count = Sum([If(day_vars[i] == city_ids[city], 1, 0) for i in range(days)])
    solver.add(count == cities[city])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(days):
        city_id = model.evaluate(day_vars[i]).as_long()
        city = id_to_city[city_id]
        itinerary.append({"day": i + 1, "place": city})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No valid itinerary found.")