import json
from z3 import *

# Define the cities and their respective stay durations
cities = {
    "Oslo": 2,
    "Helsinki": 2,
    "Edinburgh": 3,
    "Riga": 2,
    "Tallinn": 5,
    "Budapest": 5,
    "Vilnius": 5,
    "Porto": 5,
    "Geneva": 4
}

# Define the special day constraints
special_days = {
    "Oslo": [(24, 25)],
    "Tallinn": [(4, 8)]
}

# Define the flight connections
flights = [
    ("Porto", "Oslo"), ("Edinburgh", "Budapest"), ("Edinburgh", "Geneva"),
    ("Riga", "Tallinn"), ("Edinburgh", "Porto"), ("Vilnius", "Helsinki"),
    ("Tallinn", "Vilnius"), ("Riga", "Oslo"), ("Geneva", "Oslo"),
    ("Edinburgh", "Oslo"), ("Edinburgh", "Helsinki"), ("Vilnius", "Oslo"),
    ("Riga", "Helsinki"), ("Budapest", "Geneva"), ("Helsinki", "Budapest"),
    ("Helsinki", "Oslo"), ("Edinburgh", "Riga"), ("Tallinn", "Helsinki"),
    ("Geneva", "Porto"), ("Budapest", "Oslo"), ("Helsinki", "Geneva"),
    ("Riga", "Vilnius"), ("Tallinn", "Oslo")
]

# Create a solver instance
solver = Solver()

# Define variables for the start day of each city
start_vars = {city: Int(f'start_{city}') for city in cities}

# Add constraints for the start day of each city
for city, duration in cities.items():
    solver.add(start_vars[city] >= 1)
    solver.add(start_vars[city] + duration <= 25)

# Add constraints for special days
for city, day_ranges in special_days.items():
    for start, end in day_ranges:
        solver.add(Or([And(start_vars[city] <= start, start_vars[city] + cities[city] > start),
                       And(start_vars[city] <= end, start_vars[city] + cities[city] > end)]))

# Add constraints for flight connections
for city1 in cities:
    for city2 in cities:
        if city1 != city2 and ((city1, city2) in flights or (city2, city1) in flights):
            # Ensure that if moving from city1 to city2, the flight day is valid
            solver.add(Or(start_vars[city1] + cities[city1] < start_vars[city2],
                         start_vars[city2] + cities[city2] < start_vars[city1],
                         start_vars[city1] + cities[city1] == start_vars[city2],
                         start_vars[city2] + cities[city2] == start_vars[city1]))

# Ensure the itinerary covers exactly 25 days
max_end_day = Int('max_end_day')
for city, duration in cities.items():
    solver.add(max_end_day >= start_vars[city] + duration)
solver.add(max_end_day == 25)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    
    for city in cities:
        start_day = model[start_vars[city]].as_long()
        end_day = start_day + cities[city]
        itinerary.append({"day_range": f"Day {start_day}-{end_day-1}", "place": city})
        # Add flight day entries
        for i in range(start_day, end_day):
            if i != start_day:
                itinerary.append({"day_range": f"Day {i}", "place": city})
        if end_day < 26:
            next_city = None
            for c in cities:
                if model[start_vars[c]].as_long() == end_day:
                    next_city = c
                    break
            if next_city:
                itinerary.append({"day_range": f"Day {end_day-1}", "place": city})
                itinerary.append({"day_range": f"Day {end_day-1}", "place": next_city})
    
    # Sort the itinerary by day
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))
    
    print(json.dumps({"itinerary": itinerary}, indent=4))
else:
    print("No solution found")