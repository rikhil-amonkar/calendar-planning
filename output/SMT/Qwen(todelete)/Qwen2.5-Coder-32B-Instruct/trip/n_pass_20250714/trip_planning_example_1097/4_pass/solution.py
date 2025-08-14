from z3 import *
import json

# Define the number of days and cities
num_days = 18
cities = ["Reykjavik", "Riga", "Oslo", "Lyon", "Dubrovnik", "Madrid", "Warsaw", "London"]

# Create a Z3 solver instance
solver = Solver()

# Define variables for the start day of each city stay
start_vars = {city: Int(f"start_{city}") for city in cities}
end_vars = {city: Int(f"end_{city}") for city in cities}

# Define constraints for each city's stay duration
constraints = []
durations = {"Reykjavik": 4, "Riga": 2, "Oslo": 3, "Lyon": 5, "Dubrovnik": 2, "Madrid": 2, "Warsaw": 4, "London": 3}
for city, duration in durations.items():
    start = start_vars[city]
    end = end_vars[city]
    constraints.append(start >= 1)
    constraints.append(end <= num_days)
    constraints.append(end == start + duration - 1)

# Add specific constraints for meeting and attending events
constraints.append(start_vars["Riga"] == 4)  # Meet friend in Riga between day 4 and 5
constraints.append(start_vars["Dubrovnik"] == 7)  # Attend wedding in Dubrovnik between day 7 and 8

# Define possible transitions between cities via direct flights
flights = [
    ("Warsaw", "Reykjavik"), ("Oslo", "Madrid"), ("Warsaw", "Riga"), ("Lyon", "London"),
    ("Madrid", "London"), ("Warsaw", "London"), ("Reykjavik", "Madrid"), ("Warsaw", "Oslo"),
    ("Oslo", "Dubrovnik"), ("Oslo", "Reykjavik"), ("Riga", "Oslo"), ("Oslo", "Lyon"),
    ("Oslo", "London"), ("London", "Reykjavik"), ("Warsaw", "Madrid"), ("Madrid", "Lyon"),
    ("Dubrovnik", "Madrid")
]

# Add constraints for valid transitions between cities
for i in range(1, num_days):
    current_city = Or([And(start_vars[city] <= i, end_vars[city] >= i) for city in cities])
    next_city = Or([And(start_vars[city] <= i + 1, end_vars[city] >= i + 1) for city in cities])
    valid_transition = Or(Not(current_city), Not(next_city))  # No transition needed if in the same city
    for city1, city2 in flights:
        valid_transition = Or(valid_transition, And(end_vars[city1] == i, start_vars[city2] == i + 1))
        valid_transition = Or(valid_transition, And(end_vars[city2] == i, start_vars[city1] == i + 1))
    constraints.append(valid_transition)

# Ensure that the total duration of stays is exactly 18 days
total_stay_duration = Sum([end_vars[city] - start_vars[city] + 1 for city in cities])
constraints.append(total_stay_duration == num_days)

# Ensure no gaps or overlaps in the itinerary
for day in range(1, num_days + 1):
    current_day_cities = [city for city in cities if And(start_vars[city] <= day, end_vars[city] >= day)]
    constraints.append(Or([start_vars[city] <= day, end_vars[city] >= day] for city in current_day_cities))

# Add all constraints to the solver
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in range(1, num_days + 1):
        for city in cities:
            start = model[start_vars[city]].as_long()
            end = model[end_vars[city]].as_long()
            if start <= day <= end:
                if day == start:
                    itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                break
    print(json.dumps({"itinerary": itinerary}, indent=4))
else:
    print("No solution found")