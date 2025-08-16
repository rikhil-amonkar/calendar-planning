from z3 import *
import json

# Define the cities and their required durations
cities = {
    "Brussels": 3,
    "Helsinki": 3,
    "Split": 4,
    "Dubrovnik": 2,
    "Istanbul": 5,
    "Milan": 4,
    "Vilnius": 5,
    "Frankfurt": 3
}

# Direct flights between cities
direct_flights = {
    ("Milan", "Frankfurt"),
    ("Split", "Frankfurt"),
    ("Milan", "Split"),
    ("Brussels", "Vilnius"),
    ("Brussels", "Helsinki"),
    ("Istanbul", "Brussels"),
    ("Milan", "Vilnius"),
    ("Brussels", "Milan"),
    ("Istanbul", "Helsinki"),
    ("Helsinki", "Vilnius"),
    ("Helsinki", "Dubrovnik"),
    ("Split", "Vilnius"),
    ("Dubrovnik", "Istanbul"),
    ("Istanbul", "Milan"),
    ("Helsinki", "Frankfurt"),
    ("Istanbul", "Frankfurt"),
    ("Brussels", "Frankfurt"),
    ("Dubrovnik", "Frankfurt"),
    ("Frankfurt", "Vilnius")
}

# Add reverse flights since flights are direct both ways
direct_flights.update({(b, a) for a, b in direct_flights})

# Create a solver
s = Solver()

# Variables: for each day (1 to 22), the city visited
city_per_day = [String(f"day_{i}") for i in range(1, 23)]

# Constraints: each day must be one of the cities
for day in city_per_day:
    s.add(Or([day == city for city in cities]))

# Constraints: each city must be visited the required number of days
for city, days in cities.items():
    s.add(Sum([If(city_per_day[i-1] == city, 1, 0) for i in range(1, 23)]) == days)

# Constraints: direct flights between consecutive cities
for i in range(1, 22):
    prev_city = city_per_day[i-1]
    next_city = city_per_day[i]
    s.add(If(prev_city == next_city, True, (prev_city, next_city) in direct_flights))

# Constraints: Istanbul from day 1 to 5
for day in range(1, 6):
    s.add(city_per_day[day-1] == "Istanbul")

# Constraints: Workshop in Vilnius from day 18 to 22
for day in range(18, 23):
    s.add(city_per_day[day-1] == "Vilnius")

# Constraints: Wedding in Frankfurt from day 16 to 18
for day in range(16, 19):
    s.add(city_per_day[day-1] == "Frankfurt")

# Solve the problem
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(22):
        day = i + 1
        city = model[city_per_day[i]].as_string()
        itinerary.append({"day": day, "city": city})
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")