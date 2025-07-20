import json
from z3 import *

# Define the cities and their required days
cities = {
    "Stockholm": 3,
    "Hamburg": 5,
    "Florence": 2,
    "Istanbul": 5,  # Days 25-29 inclusive
    "Oslo": 5,
    "Vilnius": 5,
    "Santorini": 2,
    "Munich": 5,
    "Frankfurt": 4,
    "Krakow": 5,  # Days 5-9 inclusive
}

# Direct flights: adjacency list
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

# Create a Z3 solver
solver = Solver()

# Variables: day[i] represents the city on day i (1-based)
days = [Int(f"day_{i}") for i in range(1, 33)]  # Days 1 to 32

# Create a mapping from city names to integers
city_ids = {city: idx for idx, city in enumerate(cities.keys())}
id_to_city = {idx: city for city, idx in city_ids.items()}

# Constraints: each day must be one of the cities
for day in days:
    solver.add(Or([day == city_ids[city] for city in cities]))

# Fixed periods:
# Istanbul from day 25 to 29 (inclusive)
for i in range(25, 30):
    solver.add(days[i-1] == city_ids["Istanbul"])

# Krakow from day 5 to 9 (inclusive)
for i in range(5, 10):
    solver.add(days[i-1] == city_ids["Krakow"])

# Flight transitions: consecutive days must be either same city or connected by direct flight
for i in range(1, 32):
    current_city = days[i-1]
    next_city = days[i]
    solver.add(Or(
        current_city == next_city,
        *[And(current_city == city_ids[city1], next_city == city_ids[city2]) 
          for city1 in cities for city2 in direct_flights.get(city1, [])]
    ))

# Duration constraints: each city must be visited exactly the specified number of days
for city, count in cities.items():
    solver.add(Sum([If(days[i] == city_ids[city], 1, 0) for i in range(32)]) == count)

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(1, 33):
        city_id = model.evaluate(days[i-1]).as_long()
        city = id_to_city[city_id]
        itinerary.append({"day": i, "place": city})
    
    # Verify the counts
    counts = {city: 0 for city in cities}
    for entry in itinerary:
        counts[entry["place"]] += 1
    for city, count in cities.items():
        assert counts[city] == count, f"City {city} has {counts[city]} days instead of {count}"
    
    # Verify transitions
    for i in range(1, 32):
        current = itinerary[i-1]["place"]
        next_p = itinerary[i]["place"]
        if current != next_p:
            assert next_p in direct_flights[current], f"No flight from {current} to {next_p} on day {i+1}"
    
    # Verify fixed periods
    for day in range(25, 30):
        assert itinerary[day-1]["place"] == "Istanbul", f"Day {day} should be Istanbul"
    for day in range(5, 10):
        assert itinerary[day-1]["place"] == "Krakow", f"Day {day} should be Krakow"
    
    # Output the itinerary as JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")