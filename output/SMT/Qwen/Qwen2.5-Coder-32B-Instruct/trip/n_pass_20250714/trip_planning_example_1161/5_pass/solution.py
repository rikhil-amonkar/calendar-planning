from z3 import *

# Define the solver
solver = Solver()

# Define the variables for the start day of each city
start_days = {
    "Mykonos": Int("start_Mykonos"),
    "Krakow": Int("start_Krakow"),
    "Vilnius": Int("start_Vilnius"),
    "Helsinki": Int("start_Helsinki"),
    "Dubrovnik": Int("start_Dubrovnik"),
    "Oslo": Int("start_Oslo"),
    "Madrid": Int("start_Madrid"),
    "Paris": Int("start_Paris")
}

# Define the durations for each city
durations = {
    "Mykonos": 4,
    "Krakow": 5,
    "Vilnius": 2,
    "Helsinki": 2,
    "Dubrovnik": 3,
    "Oslo": 2,
    "Madrid": 5,
    "Paris": 2
}

# Define the constraints
for city, start_day in start_days.items():
    # Each city must start on a day between 1 and 14 (inclusive) because some cities have fixed end dates
    solver.add(start_day >= 1)
    solver.add(start_day <= 14)

# Specific constraints for Mykonos
solver.add(start_days["Mykonos"] + durations["Mykonos"] - 1 == 18)

# Specific constraints for Dubrovnik
solver.add(start_days["Dubrovnik"] <= 2)
solver.add(start_days["Dubrovnik"] + durations["Dubrovnik"] - 1 >= 4)

# Specific constraints for Oslo
solver.add(start_days["Oslo"] + durations["Oslo"] - 1 <= 2)

# Add constraints for non-overlapping stays
for i, city1 in enumerate(durations):
    for j, city2 in enumerate(durations):
        if i < j:
            # Either city1 ends before city2 starts or city2 ends before city1 starts
            solver.add(Or(start_days[city1] + durations[city1] <= start_days[city2],
                           start_days[city2] + durations[city2] <= start_days[city1]))

# Add constraints for direct flights
flight_constraints = [
    ("Oslo", "Krakow"), ("Oslo", "Paris"), ("Paris", "Madrid"), ("Helsinki", "Vilnius"),
    ("Oslo", "Madrid"), ("Oslo", "Helsinki"), ("Helsinki", "Krakow"), ("Dubrovnik", "Helsinki"),
    ("Dubrovnik", "Madrid"), ("Oslo", "Dubrovnik"), ("Krakow", "Paris"), ("Madrid", "Mykonos"),
    ("Oslo", "Vilnius"), ("Krakow", "Vilnius"), ("Helsinki", "Paris"), ("Vilnius", "Paris"),
    ("Helsinki", "Madrid")
]

# Create a mapping of city pairs to their possible flight days
flight_days = {}
for city1, city2 in flight_constraints:
    flight_days[(city1, city2)] = Int(f"flight_{city1}_{city2}")
    flight_days[(city2, city1)] = Int(f"flight_{city2}_{city1}")

# Add constraints for flight days
for (city1, city2), flight_day in flight_days.items():
    # Flight day must be within the range of the cities' stays
    solver.add(flight_day >= If(start_days[city1] > start_days[city2], start_days[city1], start_days[city2]))
    solver.add(flight_day <= If(start_days[city1] + durations[city1] - 1 < start_days[city2] + durations[city2] - 1,
                                start_days[city1] + durations[city1] - 1, start_days[city2] + durations[city2] - 1))

# Ensure the itinerary covers exactly 18 days
max_end_day = Int("max_end_day")

# Manually compute the maximum end day
end_days = [start_days[city] + durations[city] - 1 for city in durations]
solver.add(max_end_day == end_days[0])
for end_day in end_days[1:]:
    solver.add(max_end_day >= end_day)

solver.add(max_end_day == 18)

# Check if the solution is satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []

    # Add the stays in each city
    for city, start_day in start_days.items():
        start = model.evaluate(start_day).as_long()
        end = start + durations[city] - 1
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})

    # Add the flight days
    for (city1, city2), flight_day in flight_days.items():
        if model.has_interp(flight_day):
            flight = model.evaluate(flight_day).as_long()
            itinerary.append({"day_range": f"Day {flight}", "place": city1})
            itinerary.append({"day_range": f"Day {flight}", "place": city2})

    # Sort the itinerary by day
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))

    print({"itinerary": itinerary})
else:
    print("No solution found")