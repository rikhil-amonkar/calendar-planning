from z3 import *

# Define the solver
solver = Solver()

# Define the number of days
total_days = 21

# Define the cities and their respective stay durations
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

# Define the mandatory events
mandatory_events = {
    "Reykjavik": [(1, 2)],  # Conference in Reykjavik
    "Porto": [(19, 21)],   # Workshop in Porto
    "Stockholm": [(2, 4)]  # Meet a friend in Stockholm
}

# Define the direct flights
flights = [
    ("Reykjavik", "Stuttgart"), ("Reykjavik", "Stockholm"), ("Reykjavik", "Tallinn"),
    ("Stockholm", "Oslo"), ("Stuttgart", "Porto"), ("Oslo", "Split"), ("Stockholm", "Stuttgart"),
    ("Reykjavik", "Oslo"), ("Oslo", "Geneva"), ("Stockholm", "Split"), ("Reykjavik", "Stockholm"),
    ("Split", "Stuttgart"), ("Tallinn", "Oslo"), ("Stockholm", "Geneva"), ("Oslo", "Porto"),
    ("Geneva", "Porto"), ("Geneva", "Split")
]

# Create variables for the start day of each city
start_vars = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the start days of each city
for city, duration in cities.items():
    solver.add(start_vars[city] >= 1)
    solver.add(start_vars[city] + duration <= total_days)

# Add constraints for mandatory events
for city, events in mandatory_events.items():
    for start, end in events:
        solver.add(start_vars[city] <= start)
        solver.add(start_vars[city] + cities[city] >= end + 1)

# Add constraints for non-overlapping stays
for i, (city1, duration1) in enumerate(cities.items()):
    for j, (city2, duration2) in enumerate(cities.items()):
        if i < j:
            solver.add(Or(start_vars[city1] + duration1 <= start_vars[city2],
                          start_vars[city2] + duration2 <= start_vars[city1]))

# Add constraints for flights
flight_vars = {}
for (city1, city2) in flights:
    flight_vars[(city1, city2)] = Bool(f"flight_{city1}_{city2}")
    flight_vars[(city2, city1)] = Bool(f"flight_{city2}_{city1}")

# Ensure that if there's a flight from city1 to city2, it happens at the end of the stay in city1 and the start of the stay in city2
for (city1, city2) in flights:
    solver.add(Implies(flight_vars[(city1, city2)],
                       And(start_vars[city1] + cities[city1] == start_vars[city2],
                           start_vars[city1] + cities[city1] <= total_days - 1)))

# Ensure that if there's a flight from city2 to city1, it happens at the end of the stay in city2 and the start of the stay in city1
for (city1, city2) in flights:
    solver.add(Implies(flight_vars[(city2, city1)],
                       And(start_vars[city2] + cities[city2] == start_vars[city1],
                           start_vars[city2] + cities[city2] <= total_days - 1)))

# Ensure that each city is visited exactly once
visited_cities = [Bool(f"visited_{city}") for city in cities]
for i, city in enumerate(cities):
    solver.add(visited_cities[i] == Or([flight_vars[(prev_city, city)] for prev_city in cities if (prev_city, city) in flights] +
                                       [flight_vars[(city, next_city)] for next_city in cities if (city, next_city) in flights]))

# Ensure the total number of days is exactly 21
# Introduce a variable for the last city's end day
last_city_end_day = Int("last_city_end_day")

# Add constraints to find the maximum end day
max_end_day_constraints = []
for city, duration in cities.items():
    max_end_day_constraints.append(last_city_end_day >= start_vars[city] + duration)

solver.add(max_end_day_constraints)
solver.add(last_city_end_day == total_days)

# Ensure that all days are covered
days_covered = [Bool(f"day_covered_{i}") for i in range(1, total_days + 1)]

for i in range(1, total_days + 1):
    day_covered_constraint = Or([And(start_vars[city] <= i, start_vars[city] + cities[city] > i) for city in cities] +
                                [And(start_vars[city1] + cities[city1] == i, flight_vars[(city1, city2)]) for (city1, city2) in flights] +
                                [And(start_vars[city2] + cities[city2] == i, flight_vars[(city2, city1)]) for (city1, city2) in flights])
    solver.add(days_covered[i-1] == day_covered_constraint)

# Ensure that all days are covered
solver.add(And(days_covered))

# Manually specify some initial constraints to help the solver
solver.add(start_vars["Reykjavik"] == 1)  # Start in Reykjavik for the conference
solver.add(start_vars["Porto"] == 19)     # End in Porto for the workshop
solver.add(start_vars["Stockholm"] == 2)  # Visit Stockholm for the meeting

# Check if the solution is satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city, start_var in start_vars.items():
        start_day = model[start_var].as_long()
        end_day = start_day + cities[city] - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        # Add flight days
        for (city1, city2) in flights:
            if model.evaluate(flight_vars[(city1, city2)]) and city1 == city:
                itinerary.append({"day_range": f"Day {end_day+1}", "place": city1})
                itinerary.append({"day_range": f"Day {end_day+1}", "place": city2})
            elif model.evaluate(flight_vars[(city2, city1)]) and city2 == city:
                itinerary.append({"day_range": f"Day {end_day+1}", "place": city2})
                itinerary.append({"day_range": f"Day {end_day+1}", "place": city1})

    # Sort the itinerary by day
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))

    print({"itinerary": itinerary})
else:
    print("No solution found")