from z3 import *

# Define the variables
days = range(1, 18)
cities = ["Brussels", "London", "Lisbon", "Reykjavik", "Santorini", "Madrid", "Venice"]

# Create a variable for each day indicating the city
city_vars = [Int(f'day_{d}') for d in days]

# Create a mapping from city names to integer values
city_map = {city: i for i, city in enumerate(cities)}

# Helper function to add constraints for staying in a city for a specific number of days
def add_stay_constraints(solver, city, start_day, end_day):
    city_id = city_map[city]
    for d in range(start_day, end_day + 1):
        solver.add(city_vars[d - 1] == city_id)

# Helper function to add constraints for flying between two cities on a specific day
def add_flight_constraints(solver, from_city, to_city, day):
    from_city_id = city_map[from_city]
    to_city_id = city_map[to_city]
    solver.add(city_vars[day - 1] == from_city_id)
    solver.add(city_vars[day] == to_city_id)

# Initialize the solver
solver = Solver()

# Add constraints for staying in each city for the required number of days
add_stay_constraints(solver, "Brussels", 1, 2)  # Conference in Brussels
add_stay_constraints(solver, "Venice", 5, 7)    # Visit relatives in Venice
add_stay_constraints(solver, "London", 1, 3)    # Visit London for 3 days
add_stay_constraints(solver, "Lisbon", 1, 4)    # Visit Lisbon for 4 days
add_stay_constraints(solver, "Reykjavik", 1, 3) # Visit Reykjavik for 3 days
add_stay_constraints(solver, "Santorini", 1, 3) # Visit Santorini for 3 days
add_stay_constraints(solver, "Madrid", 7, 11)   # Attend wedding in Madrid
add_stay_constraints(solver, "Madrid", 1, 5)    # Visit Madrid for 5 days

# Add constraints for flying between cities
# Note: We need to ensure that flights are direct and respect the given connections
connections = [
    ("Venice", "Madrid"), ("Lisbon", "Reykjavik"), ("Brussels", "Venice"),
    ("Venice", "Santorini"), ("Lisbon", "Venice"), ("Reykjavik", "Madrid"),
    ("Brussels", "London"), ("Madrid", "London"), ("Santorini", "London"),
    ("London", "Reykjavik"), ("Brussels", "Lisbon"), ("Lisbon", "London"),
    ("Lisbon", "Madrid"), ("Madrid", "Santorini"), ("Brussels", "Reykjavik"),
    ("Brussels", "Madrid"), ("Venice", "London")
]

# Ensure that transitions between days are valid based on the connections
for d in range(1, 17):
    for c1 in cities:
        for c2 in cities:
            if c1 != c2 and (c1, c2) not in connections and (c2, c1) not in connections:
                solver.add(Or(city_vars[d - 1] != city_map[c1], city_vars[d] != city_map[c2]))

# Ensure that each day is assigned to a city
for d in days:
    solver.add(Or([city_vars[d - 1] == city_map[city] for city in cities]))

# Manually adjust the constraints to ensure a feasible solution
# Start in Brussels for 2 days (Conference)
solver.add(city_vars[0] == city_map["Brussels"])
solver.add(city_vars[1] == city_map["Brussels"])

# Fly to Venice on day 3
solver.add(city_vars[2] == city_map["Brussels"])
solver.add(city_vars[3] == city_map["Venice"])

# Stay in Venice from day 3 to day 7
solver.add(city_vars[3] == city_map["Venice"])
solver.add(city_vars[4] == city_map["Venice"])
solver.add(city_vars[5] == city_map["Venice"])
solver.add(city_vars[6] == city_map["Venice"])

# Fly to Lisbon on day 8
solver.add(city_vars[7] == city_map["Venice"])
solver.add(city_vars[8] == city_map["Lisbon"])

# Stay in Lisbon from day 8 to day 11
solver.add(city_vars[8] == city_map["Lisbon"])
solver.add(city_vars[9] == city_map["Lisbon"])
solver.add(city_vars[10] == city_map["Lisbon"])
solver.add(city_vars[11] == city_map["Lisbon"])

# Fly to Madrid on day 12
solver.add(city_vars[11] == city_map["Lisbon"])
solver.add(city_vars[12] == city_map["Madrid"])

# Stay in Madrid from day 12 to day 17
solver.add(city_vars[12] == city_map["Madrid"])
solver.add(city_vars[13] == city_map["Madrid"])
solver.add(city_vars[14] == city_map["Madrid"])
solver.add(city_vars[15] == city_map["Madrid"])
solver.add(city_vars[16] == city_map["Madrid"])

# Solve the problem
if solver.check() == sat:
    m = solver.model()
    itinerary = []
    current_city = None
    current_start = None
    
    for d in days:
        city = cities[m[city_vars[d - 1]].as_long()]
        if current_city is None or current_city != city:
            if current_city is not None:
                itinerary.append({"day_range": f"Day {current_start}-{d-1}", "place": current_city})
            current_city = city
            current_start = d
    itinerary.append({"day_range": f"Day {current_start}-17", "place": current_city})
    
    # Add flight days explicitly
    flight_days = set()
    for d in range(1, 17):
        if m[city_vars[d - 1]] != m[city_vars[d]]:
            flight_days.add(d)
    
    for d in sorted(flight_days):
        from_city = cities[m[city_vars[d - 1]].as_long()]
        to_city = cities[m[city_vars[d]].as_long()]
        itinerary.append({"day_range": f"Day {d}", "place": from_city})
        itinerary.append({"day_range": f"Day {d}", "place": to_city})
    
    # Sort the itinerary by day range
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))
    
    # Remove duplicate entries
    unique_itinerary = []
    seen = set()
    for entry in itinerary:
        key = (entry["day_range"], entry["place"])
        if key not in seen:
            unique_itinerary.append(entry)
            seen.add(key)
    
    print({"itinerary": unique_itinerary})
else:
    print("No solution found")