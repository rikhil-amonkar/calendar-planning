import json
from z3 import *

# Define the cities
cities = [
    "Santorini", "Valencia", "Madrid", "Seville", "Bucharest", 
    "Vienna", "Riga", "Tallinn", "Krakow", "Frankfurt"
]

# Define the direct flight connections as a dictionary
direct_flights = {
    "Vienna": ["Bucharest", "Seville", "Valencia", "Madrid", "Krakow", "Frankfurt", "Riga"],
    "Bucharest": ["Vienna", "Riga", "Valencia", "Santorini", "Madrid", "Frankfurt"],
    "Santorini": ["Madrid", "Bucharest", "Vienna"],
    "Madrid": ["Santorini", "Valencia", "Seville", "Vienna", "Bucharest", "Frankfurt"],
    "Seville": ["Valencia", "Vienna", "Madrid"],
    "Valencia": ["Seville", "Madrid", "Bucharest", "Vienna", "Krakow", "Frankfurt"],
    "Riga": ["Bucharest", "Vienna", "Tallinn", "Frankfurt"],
    "Tallinn": ["Riga", "Frankfurt"],
    "Krakow": ["Valencia", "Frankfurt", "Vienna"],
    "Frankfurt": ["Valencia", "Krakow", "Vienna", "Riga", "Tallinn", "Bucharest", "Madrid"]
}

# Create a Z3 solver instance
s = Solver()

# Create variables for each day (1-based index)
day_vars = [Int(f"day_{i}") for i in range(1, 28)]

# Each day variable must be an index corresponding to a city (0 to 9)
for day in day_vars:
    s.add(day >= 0, day < len(cities))

# Add constraints for each city's required days
# Santorini: 3 days
s.add(Sum([If(day_vars[i] == cities.index("Santorini"), 1, 0) for i in range(27)]) == 3)
# Valencia: 4 days
s.add(Sum([If(day_vars[i] == cities.index("Valencia"), 1, 0) for i in range(27)]) == 4)
# Madrid: 2 days
s.add(Sum([If(day_vars[i] == cities.index("Madrid"), 1, 0) for i in range(27)]) == 2)
# Seville: 2 days
s.add(Sum([If(day_vars[i] == cities.index("Seville"), 1, 0) for i in range(27)]) == 2)
# Bucharest: 3 days
s.add(Sum([If(day_vars[i] == cities.index("Bucharest"), 1, 0) for i in range(27)]) == 3)
# Vienna: 4 days
s.add(Sum([If(day_vars[i] == cities.index("Vienna"), 1, 0) for i in range(27)]) == 4)
# Riga: 4 days
s.add(Sum([If(day_vars[i] == cities.index("Riga"), 1, 0) for i in range(27)]) == 4)
# Tallinn: 5 days
s.add(Sum([If(day_vars[i] == cities.index("Tallinn"), 1, 0) for i in range(27)]) == 5)
# Krakow: 5 days
s.add(Sum([If(day_vars[i] == cities.index("Krakow"), 1, 0) for i in range(27)]) == 5)
# Frankfurt: 4 days
s.add(Sum([If(day_vars[i] == cities.index("Frankfurt"), 1, 0) for i in range(27)]) == 4)

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

# Add constraints for flight transitions: consecutive days must be either same city or connected by direct flight
for i in range(26):
    current_city = day_vars[i]
    next_city = day_vars[i+1]
    # Either stay in the same city or move to a connected city
    s.add(Or(
        current_city == next_city,
        And(current_city != next_city, 
            cities[next_city] in direct_flights[cities[current_city]])
    ))

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