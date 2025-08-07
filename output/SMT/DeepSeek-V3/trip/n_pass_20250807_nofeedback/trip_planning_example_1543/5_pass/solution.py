import json
from z3 import *

# Define cities and required days
cities = {
    "Prague": 3,
    "Warsaw": 4,
    "Dublin": 3,
    "Athens": 3,
    "Vilnius": 4,
    "Porto": 5,
    "London": 3,
    "Seville": 2,
    "Lisbon": 5,
    "Dubrovnik": 3
}

# Direct flights (bidirectional)
direct_flights = [
    ("Warsaw", "Vilnius"), ("Prague", "Athens"), ("London", "Lisbon"),
    ("Lisbon", "Porto"), ("Prague", "Lisbon"), ("London", "Dublin"),
    ("Athens", "Vilnius"), ("Athens", "Dublin"), ("Prague", "London"),
    ("London", "Warsaw"), ("Dublin", "Seville"), ("Seville", "Porto"),
    ("Lisbon", "Athens"), ("Dublin", "Porto"), ("Athens", "Warsaw"),
    ("Lisbon", "Warsaw"), ("Porto", "Warsaw"), ("Prague", "Warsaw"),
    ("Prague", "Dublin"), ("Athens", "Dubrovnik"), ("Lisbon", "Dublin"),
    ("Dubrovnik", "Dublin"), ("Lisbon", "Seville"), ("London", "Athens")
]

# Make flights bidirectional
flight_set = set()
for a, b in direct_flights:
    flight_set.add((a, b))
    flight_set.add((b, a))

# Create solver
s = Solver()

# Day variables (1-26)
day_vars = [Int(f"day_{i}") for i in range(1, 27)]

# City mapping
city_ids = {city: i for i, city in enumerate(cities)}
id_to_city = {i: city for city, i in city_ids.items()}

# Each day must be a valid city
for day in day_vars:
    s.add(day >= 0, day < len(cities))

# Hard constraints
# Prague must include days 1-3 (workshop)
s.add(day_vars[0] == city_ids["Prague"])
s.add(day_vars[1] == city_ids["Prague"])
s.add(day_vars[2] == city_ids["Prague"])

# London must include days 3-5 (wedding)
s.add(day_vars[2] == city_ids["London"])
s.add(day_vars[3] == city_ids["London"])
s.add(day_vars[4] == city_ids["London"])

# Lisbon must include days 5-9 (relatives)
for i in range(4, 9):
    s.add(day_vars[i] == city_ids["Lisbon"])

# Porto must include days 16-20 (conference)
for i in range(15, 20):
    s.add(day_vars[i] == city_ids["Porto"])

# Warsaw must include days 20-23 (friends)
for i in range(19, 23):
    s.add(day_vars[i] == city_ids["Warsaw"])

# Flight connections between consecutive days
for i in range(25):
    current = day_vars[i]
    next_day = day_vars[i+1]
    s.add(Or(
        current == next_day,
        *[And(current == city_ids[a], next_day == city_ids[b]) for a, b in flight_set]
    ))

# Total days per city
for city, days_needed in cities.items():
    s.add(Sum([If(d == city_ids[city], 1, 0) for d in day_vars]) == days_needed)

# Solve
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(26):
        city_id = model.evaluate(day_vars[i]).as_long()
        itinerary.append({"day": i+1, "place": id_to_city[city_id]})
    
    # Verify solution
    city_days = {city: 0 for city in cities}
    for day in itinerary:
        city_days[day["place"]] += 1
    
    for city, days_needed in cities.items():
        assert city_days[city] == days_needed, f"{city} day count mismatch"
    
    # Verify flights
    for i in range(25):
        curr = itinerary[i]["place"]
        next_p = itinerary[i+1]["place"]
        if curr != next_p:
            assert (curr, next_p) in flight_set, f"No flight from {curr} to {next_p}"
    
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")