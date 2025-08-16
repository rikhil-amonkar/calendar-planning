from z3 import *
import json

# Define the cities as an EnumSort
cities = ["Helsinki", "Warsaw", "Madrid", "Split", "Reykjavik", "Budapest"]
City = Datatype('City')
for city in cities:
    City.declare(city)
City = City.create()

# Direct flights as per the problem statement
direct_flights = [
    (City.Helsinki, City.Reykjavik),
    (City.Reykjavik, City.Helsinki),
    (City.Budapest, City.Warsaw),
    (City.Warsaw, City.Budapest),
    (City.Madrid, City.Split),
    (City.Split, City.Madrid),
    (City.Helsinki, City.Split),
    (City.Split, City.Helsinki),
    (City.Helsinki, City.Madrid),
    (City.Madrid, City.Helsinki),
    (City.Helsinki, City.Budapest),
    (City.Budapest, City.Helsinki),
    (City.Reykjavik, City.Warsaw),
    (City.Warsaw, City.Reykjavik),
    (City.Helsinki, City.Warsaw),
    (City.Warsaw, City.Helsinki),
    (City.Madrid, City.Budapest),
    (City.Budapest, City.Madrid),
    (City.Budapest, City.Reykjavik),
    (City.Reykjavik, City.Budapest),
    (City.Madrid, City.Warsaw),
    (City.Warsaw, City.Madrid),
    (City.Warsaw, City.Split),
    (City.Split, City.Warsaw),
    (City.Reykjavik, City.Madrid),
]

# Create 14 variables for each day (0-based index)
current_city = [Const(f'current_city_{i}', City) for i in range(14)]

# Solver instance
solver = Solver()

# Add specific day constraints
# Day 1 and 2: Helsinki
solver.add(current_city[0] == City.Helsinki)
solver.add(current_city[1] == City.Helsinki)

# Day 8: Reykjavik
solver.add(current_city[7] == City.Reykjavik)

# Day 9-11: Warsaw
solver.add(current_city[8] == City.Warsaw)
solver.add(current_city[9] == City.Warsaw)
solver.add(current_city[10] == City.Warsaw)

# Add flight constraints
for i in range(13):
    # If there is a flight from current_city[i] to current_city[i+1], it must be a direct flight
    flight_allowed = Or([And(current_city[i] == a, current_city[i+1] == b) for a, b in direct_flights])
    solver.add(Implies(current_city[i] != current_city[i+1], flight_allowed))

# Required days for each city
required_days = {
    City.Helsinki: 2,
    City.Warsaw: 3,
    City.Madrid: 4,
    City.Split: 4,
    City.Reykjavik: 2,
    City.Budapest: 4,
}

# Add constraints for the total days spent in each city
for city, req in required_days.items():
    current_city_count = Sum([If(current_city[i] == city, 1, 0) for i in range(14)])
    departure_count = Sum([If(And(current_city[i] == city, current_city[i] != current_city[i+1]), 1, 0) for i in range(13)])
    total_count = current_city_count + departure_count
    solver.add(total_count == req)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Extract the itinerary
    itinerary = []
    for day in range(1, 15):
        city = model.evaluate(current_city[day-1])
        city_name = city.decl().name()
        itinerary.append({"day": day, "city": city_name})
    
    # Output the JSON
    print(json.dumps({"itinerary": itinerary}, indent=4))
else:
    print("No solution found.")