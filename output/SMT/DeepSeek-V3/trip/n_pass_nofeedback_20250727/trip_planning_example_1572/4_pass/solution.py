import json
from z3 import *

# Define the cities and their required days
cities = {
    "Lyon": 3,
    "Paris": 5,
    "Riga": 2,
    "Berlin": 2,
    "Stockholm": 3,
    "Zurich": 5,
    "Nice": 2,
    "Seville": 3,
    "Milan": 3,
    "Naples": 4
}

# Define direct flight connections as a set of tuples
direct_flights = {
    ("Paris", "Stockholm"),
    ("Seville", "Paris"),
    ("Naples", "Zurich"),
    ("Nice", "Riga"),
    ("Berlin", "Milan"),
    ("Paris", "Zurich"),
    ("Paris", "Nice"),
    ("Milan", "Paris"),
    ("Milan", "Riga"),
    ("Paris", "Lyon"),
    ("Milan", "Naples"),
    ("Paris", "Riga"),
    ("Berlin", "Stockholm"),
    ("Stockholm", "Riga"),
    ("Nice", "Zurich"),
    ("Milan", "Zurich"),
    ("Lyon", "Nice"),
    ("Zurich", "Stockholm"),
    ("Zurich", "Riga"),
    ("Berlin", "Naples"),
    ("Milan", "Stockholm"),
    ("Berlin", "Zurich"),
    ("Milan", "Seville"),
    ("Paris", "Naples"),
    ("Berlin", "Riga"),
    ("Nice", "Stockholm"),
    ("Berlin", "Paris"),
    ("Nice", "Naples"),
    ("Berlin", "Nice")
}

# Create a dictionary to map city names to integers for Z3
city_names = sorted(cities.keys())
city_to_int = {city: idx for idx, city in enumerate(city_names)}
int_to_city = {idx: city for idx, city in enumerate(city_names)}

# Number of days
num_days = 23

# Create Z3 solver
s = Solver()

# Variables: day[i] is the city on day i+1 (days are 1-based)
day = [Int(f"day_{i}") for i in range(num_days)]

# Each day must be one of the cities
for d in day:
    s.add(And(d >= 0, d < len(city_names)))

# Constraints for fixed days
# Berlin includes day 1 and 2 (wedding between day 1 and 2)
s.add(day[0] == city_to_int["Berlin"])  # Day 1 is Berlin
s.add(day[1] == city_to_int["Berlin"])  # Day 2 is Berlin

# Stockholm includes days 20-22 (annual show)
s.add(day[19] == city_to_int["Stockholm"])  # Day 20
s.add(day[20] == city_to_int["Stockholm"])  # Day 21
s.add(day[21] == city_to_int["Stockholm"])  # Day 22

# Nice includes days 12 and 13 (workshop)
s.add(day[11] == city_to_int["Nice"])  # Day 12
s.add(day[12] == city_to_int["Nice"])  # Day 13

# Transition constraints: consecutive days must be connected by a direct flight
for i in range(num_days - 1):
    current_city = day[i]
    next_city = day[i + 1]
    # The flight must exist between current_city and next_city
    s.add(Or(*[
        And(current_city == city_to_int[a], next_city == city_to_int[b])
        for a, b in direct_flights
    ] + [
        And(current_city == city_to_int[b], next_city == city_to_int[a])
        for a, b in direct_flights
    ]))

# Constraints for the total days in each city
for city, required_days in cities.items():
    city_idx = city_to_int[city]
    s.add(Sum([If(d == city_idx, 1, 0) for d in day]) == required_days)

# Solve the problem
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(num_days):
        city_idx = model.evaluate(day[i]).as_long()
        itinerary.append({"day": i + 1, "place": int_to_city[city_idx]})
    
    # Prepare the output
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")