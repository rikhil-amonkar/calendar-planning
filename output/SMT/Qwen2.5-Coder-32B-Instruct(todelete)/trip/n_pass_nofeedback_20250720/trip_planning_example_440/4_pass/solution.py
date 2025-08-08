from z3 import *

# Define the cities
cities = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]

# Define the number of days to stay in each city
days_in_city = {
    "Split": 2,
    "Helsinki": 2,
    "Reykjavik": 3,
    "Vilnius": 3,
    "Geneva": 6
}

# Define the special constraints
wedding_days = (10, 12)  # Days 10-12 in Reykjavik
relatives_days = (7, 9)  # Days 7-9 in Vilnius

# Define the direct flights
direct_flights = {
    ("Split", "Helsinki"),
    ("Geneva", "Split"),
    ("Geneva", "Helsinki"),
    ("Helsinki", "Reykjavik"),
    ("Vilnius", "Helsinki"),
    ("Split", "Vilnius")
}

# Create a solver
solver = Solver()

# Define the start day for each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the number of days in each city
for city, days in days_in_city.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + days <= 12)

# Add constraints for the special events
# Wedding in Reykjavik between day 10 and day 12
solver.add(Or(
    And(start_days["Reykjavik"] <= 10, start_days["Reykjavik"] + days_in_city["Reykjavik"] >= 10),
    And(start_days["Reykjavik"] <= 11, start_days["Reykjavik"] + days_in_city["Reykjavik"] >= 11),
    And(start_days["Reykjavik"] <= 12, start_days["Reykjavik"] + days_in_city["Reykjavik"] >= 12)
))

# Visit relatives in Vilnius between day 7 and day 9
solver.add(Or(
    And(start_days["Vilnius"] <= 7, start_days["Vilnius"] + days_in_city["Vilnius"] >= 7),
    And(start_days["Vilnius"] <= 8, start_days["Vilnius"] + days_in_city["Vilnius"] >= 8),
    And(start_days["Vilnius"] <= 9, start_days["Vilnius"] + days_in_city["Vilnius"] >= 9)
))

# Add constraints for direct flights
for i in range(len(cities)):
    for j in range(i + 1, len(cities)):
        city1, city2 = cities[i], cities[j]
        if (city1, city2) in direct_flights or (city2, city1) in direct_flights:
            # If you leave city1 on day X, you must arrive in city2 on day X or later
            solver.add(Or(
                start_days[city1] + days_in_city[city1] < start_days[city2],
                start_days[city2] + days_in_city[city2] < start_days[city1],
                And(start_days[city1] + days_in_city[city1] == start_days[city2], (city1, city2) in direct_flights),
                And(start_days[city2] + days_in_city[city2] == start_days[city1], (city2, city1) in direct_flights)
            ))
        else:
            # If there is no direct flight, you cannot switch between these cities on the same day
            solver.add(Or(
                start_days[city1] + days_in_city[city1] < start_days[city2],
                start_days[city2] + days_in_city[city2] < start_days[city1]
            ))

# Ensure that the total number of days is exactly 12
# Create a list of all days
all_days = [Bool(f"day_{d}_{city}") for d in range(1, 13) for city in cities]

# Add constraints for each day
for d in range(1, 13):
    # Exactly one city per day
    solver.add(AtMost(*[all_days[(d-1)*len(cities) + i] for i in range(len(cities))], 1))
    solver.add(AtLeast(*[all_days[(d-1)*len(cities) + i] for i in range(len(cities))], 1))

# Add constraints for each city
for city in cities:
    start = start_days[city]
    days = days_in_city[city]
    for d in range(1, 13):
        # Use If to handle symbolic expressions
        solver.add(If(Or(d < start, d >= start + days), Not(all_days[(d-1)*len(cities) + cities.index(city)]), True))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for d in range(1, 13):
        for city in cities:
            if model.evaluate(all_days[(d-1)*len(cities) + cities.index(city)]):
                itinerary.append((d, city))
    itinerary_dict = {"itinerary": [{"day": day, "place": place} for day, place in itinerary]}
    print(itinerary_dict)
else:
    print("No solution found")