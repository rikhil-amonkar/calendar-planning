import json
from z3 import *

# Define the cities
cities = [
    "Santorini", "Valencia", "Madrid", "Seville", "Bucharest", 
    "Vienna", "Riga", "Tallinn", "Krakow", "Frankfurt"
]

# Define the direct flight connections as a set of tuples
flight_connections = [
    ("Vienna", "Bucharest"), ("Vienna", "Seville"), ("Vienna", "Valencia"),
    ("Vienna", "Madrid"), ("Vienna", "Krakow"), ("Vienna", "Frankfurt"),
    ("Vienna", "Riga"), ("Bucharest", "Vienna"), ("Bucharest", "Riga"),
    ("Bucharest", "Valencia"), ("Bucharest", "Santorini"), ("Bucharest", "Madrid"),
    ("Bucharest", "Frankfurt"), ("Santorini", "Madrid"), ("Santorini", "Bucharest"),
    ("Santorini", "Vienna"), ("Madrid", "Santorini"), ("Madrid", "Valencia"),
    ("Madrid", "Seville"), ("Madrid", "Vienna"), ("Madrid", "Bucharest"),
    ("Madrid", "Frankfurt"), ("Seville", "Valencia"), ("Seville", "Vienna"),
    ("Seville", "Madrid"), ("Valencia", "Seville"), ("Valencia", "Madrid"),
    ("Valencia", "Bucharest"), ("Valencia", "Vienna"), ("Valencia", "Krakow"),
    ("Valencia", "Frankfurt"), ("Riga", "Bucharest"), ("Riga", "Vienna"),
    ("Riga", "Tallinn"), ("Riga", "Frankfurt"), ("Tallinn", "Riga"),
    ("Tallinn", "Frankfurt"), ("Krakow", "Valencia"), ("Krakow", "Frankfurt"),
    ("Krakow", "Vienna"), ("Frankfurt", "Valencia"), ("Frankfurt", "Krakow"),
    ("Frankfurt", "Vienna"), ("Frankfurt", "Riga"), ("Frankfurt", "Tallinn"),
    ("Frankfurt", "Bucharest"), ("Frankfurt", "Madrid")
]

# Create a Z3 solver instance
s = Solver()

# Create variables for each day (1-based index)
day_vars = [Int(f"day_{i}") for i in range(1, 28)]

# Each day variable must be an index corresponding to a city (0 to 9)
for day in day_vars:
    s.add(day >= 0, day < len(cities))

# Add constraints for each city's required days
city_days = {
    "Santorini": 3,
    "Valencia": 4,
    "Madrid": 2,
    "Seville": 2,
    "Bucharest": 3,
    "Vienna": 4,
    "Riga": 4,
    "Tallinn": 5,
    "Krakow": 5,
    "Frankfurt": 4
}

for city, days in city_days.items():
    s.add(Sum([If(day_vars[i] == cities.index(city), 1, 0) for i in range(27)]) == days)

# Add constraints for specific events
# Madrid: annual show on day 6-7 (0-based: days 5-6)
s.add(day_vars[5] == cities.index("Madrid"))
s.add(day_vars[6] == cities.index("Madrid"))
# Vienna: wedding between day 3-6 (0-based: days 2-5)
s.add(Or([day_vars[i] == cities.index("Vienna") for i in range(2, 6)]))
# Riga: conference day 20-23 (0-based: days 19-22)
for i in range(19, 23):
    s.add(day_vars[i] == cities.index("Riga"))
# Tallinn: workshop day 23-27 (0-based: days 22-26)
for i in range(22, 27):
    s.add(day_vars[i] == cities.index("Tallinn"))
# Krakow: friends tour day 11-15 (0-based: days 10-14)
for i in range(10, 15):
    s.add(day_vars[i] == cities.index("Krakow"))

# Add constraints for flight transitions
for i in range(26):
    current = day_vars[i]
    next_day = day_vars[i+1]
    # Either stay in same city or have a direct flight
    same_city = current == next_day
    flight_options = []
    for (c1, c2) in flight_connections:
        flight_options.append(And(current == cities.index(c1), next_day == cities.index(c2)))
    s.add(Or(same_city, *flight_options))

# Check if the problem is satisfiable
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(27):
        day = i + 1
        city_index = m.evaluate(day_vars[i]).as_long()
        city = cities[city_index]
        itinerary.append({"day": day, "place": city})
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No valid itinerary found.")