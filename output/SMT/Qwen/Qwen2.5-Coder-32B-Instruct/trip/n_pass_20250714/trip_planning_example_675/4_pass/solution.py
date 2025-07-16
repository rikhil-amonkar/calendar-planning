from z3 import *
import json

# Define the solver
solver = Solver()

# Define the variables
days = range(1, 17)
cities = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
city_vars = {city: [Bool(f"{city}_day_{day}") for day in days] for city in cities}

# Constraints based on the problem statement

# Stay in Dubrovnik for 4 days (Days 1-4)
for day in range(1, 5):
    solver.add(city_vars['Dubrovnik'][day-1])
for day in range(5, 17):
    solver.add(Not(city_vars['Dubrovnik'][day-1]))

# Stay in Split for 3 days (Days 9-11)
for day in range(9, 12):
    solver.add(city_vars['Split'][day-1])
for day in range(1, 9) + range(12, 17):
    solver.add(Not(city_vars['Split'][day-1]))

# Stay in Milan for 3 days (Days 11-13)
for day in range(11, 14):
    solver.add(city_vars['Milan'][day-1])
for day in range(1, 11) + range(14, 17):
    solver.add(Not(city_vars['Milan'][day-1]))

# Stay in Porto for 4 days (Days 13-16)
for day in range(13, 17):
    solver.add(city_vars['Porto'][day-1])
for day in range(1, 13):
    solver.add(Not(city_vars['Porto'][day-1]))

# Stay in Krakow for 2 days (Days 8-9)
for day in range(8, 10):
    solver.add(city_vars['Krakow'][day-1])
for day in range(1, 8) + range(10, 17):
    solver.add(Not(city_vars['Krakow'][day-1]))

# Stay in Munich for 5 days (Days 4-8)
for day in range(4, 9):
    solver.add(city_vars['Munich'][day-1])
for day in range(1, 4) + range(9, 17):
    solver.add(Not(city_vars['Munich'][day-1]))

# Direct flight constraints
solver.add(city_vars['Dubrovnik'][3])  # Fly from Dubrovnik to Munich on Day 4
solver.add(city_vars['Munich'][3])     # Arrive in Munich on Day 4
solver.add(city_vars['Munich'][7])     # Fly from Munich to Krakow on Day 8
solver.add(city_vars['Krakow'][7])     # Arrive in Krakow on Day 8
solver.add(city_vars['Krakow'][8])     # Fly from Krakow to Split on Day 9
solver.add(city_vars['Split'][8])      # Arrive in Split on Day 9
solver.add(city_vars['Split'][10])     # Fly from Split to Milan on Day 11
solver.add(city_vars['Milan'][10])     # Arrive in Milan on Day 11
solver.add(city_vars['Milan'][12])     # Fly from Milan to Porto on Day 13
solver.add(city_vars['Porto'][12])     # Arrive in Porto on Day 13

# Ensure that only one city is visited per day
for day in days:
    solver.add(AtMost(*[city_vars[city][day-1] for city in cities], 1))
    solver.add(AtLeast(*[city_vars[city][day-1] for city in cities], 1))

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in days:
        for city in cities:
            if model.evaluate(city_vars[city][day-1]):
                itinerary.append({"day_range": f"Day {day}", "place": city})
    # Merge consecutive days in the same city
    merged_itinerary = []
    current_city = None
    start_day = None
    for entry in itinerary:
        if current_city != entry["place"]:
            if current_city is not None:
                merged_itinerary.append({"day_range": f"Day {start_day}-{entry['day_range'].split()[1]}" if entry['day_range'].split()[1] != str(start_day) else f"Day {start_day}", "place": current_city})
            current_city = entry["place"]
            start_day = entry['day_range'].split()[1]
    if current_city is not None:
        merged_itinerary.append({"day_range": f"Day {start_day}-{days[-1]}" if days[-1] != int(start_day) else f"Day {start_day}", "place": current_city})
    
    print(json.dumps({"itinerary": merged_itinerary}, indent=4))
else:
    print("No solution found")