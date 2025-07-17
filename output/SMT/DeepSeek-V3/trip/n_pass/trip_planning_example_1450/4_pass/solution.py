import json
from z3 import *

# Define cities and their required days
cities = {
    "Stockholm": 3,
    "Hamburg": 5,
    "Florence": 2,
    "Istanbul": 5,
    "Oslo": 5,
    "Vilnius": 5,
    "Santorini": 2,
    "Munich": 5,
    "Frankfurt": 4,
    "Krakow": 5,
}

# Direct flight connections
direct_flights = {
    "Oslo": ["Stockholm", "Istanbul", "Krakow", "Vilnius", "Frankfurt", "Hamburg", "Munich"],
    "Stockholm": ["Oslo", "Munich", "Hamburg", "Istanbul", "Santorini", "Frankfurt", "Krakow"],
    "Krakow": ["Frankfurt", "Istanbul", "Vilnius", "Oslo", "Munich", "Stockholm"],
    "Frankfurt": ["Krakow", "Istanbul", "Florence", "Oslo", "Stockholm", "Munich", "Hamburg", "Vilnius"],
    "Istanbul": ["Krakow", "Oslo", "Vilnius", "Frankfurt", "Munich", "Hamburg", "Stockholm"],
    "Vilnius": ["Istanbul", "Oslo", "Frankfurt", "Munich", "Krakow"],
    "Munich": ["Stockholm", "Hamburg", "Istanbul", "Oslo", "Frankfurt", "Florence", "Krakow", "Vilnius"],
    "Hamburg": ["Stockholm", "Munich", "Istanbul", "Oslo", "Frankfurt"],
    "Florence": ["Frankfurt", "Munich"],
    "Santorini": ["Stockholm", "Oslo"],
}

# Create solver
solver = Solver()

# Day variables (1-32)
days = [Int(f'day_{i}') for i in range(1, 33)]

# City mapping
city_ids = {city: idx for idx, city in enumerate(cities)}
id_to_city = {idx: city for city, idx in city_ids.items()}

# Each day must be one of the cities
for day in days:
    solver.add(Or([day == city_ids[city] for city in cities]))

# Fixed periods
for i in range(25, 30):  # Istanbul days 25-29
    solver.add(days[i-1] == city_ids["Istanbul"])
for i in range(5, 10):   # Krakow days 5-9
    solver.add(days[i-1] == city_ids["Krakow"])

# Flight transitions
for i in range(31):
    current = days[i]
    next_day = days[i+1]
    solver.add(Or(
        current == next_day,
        *[And(current == city_ids[c1], next_day == city_ids[c2]) 
          for c1 in cities for c2 in direct_flights.get(c1, [])]
    ))

# Duration constraints
for city, count in cities.items():
    solver.add(Sum([If(days[i] == city_ids[city], 1, 0) for i in range(32)]) == count)

# Solve
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(32):
        city_id = model.evaluate(days[i]).as_long()
        itinerary.append({"day": i+1, "place": id_to_city[city_id]})
    
    # Verify counts
    counts = {city: 0 for city in cities}
    for entry in itinerary:
        counts[entry["place"]] += 1
    for city, count in cities.items():
        assert counts[city] == count, f"City {city} has wrong day count"
    
    # Verify transitions
    for i in range(31):
        current = itinerary[i]["place"]
        next_p = itinerary[i+1]["place"]
        if current != next_p:
            assert next_p in direct_flights[current], f"Invalid flight {current}->{next_p}"
    
    # Verify fixed periods
    for day in range(25, 30):
        assert itinerary[day-1]["place"] == "Istanbul"
    for day in range(5, 10):
        assert itinerary[day-1]["place"] == "Krakow"
    
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")