import json
from z3 import *

# Define cities and required days
cities = {
    "Salzburg": 2,
    "Venice": 5,
    "Bucharest": 4,
    "Brussels": 2,
    "Hamburg": 4,
    "Copenhagen": 4,
    "Nice": 3,
    "Zurich": 5,
    "Naples": 4
}

# Direct flight connections
direct_flights = {
    "Zurich": ["Brussels", "Nice", "Naples", "Copenhagen", "Venice", "Bucharest", "Hamburg"],
    "Brussels": ["Zurich", "Venice", "Bucharest", "Hamburg", "Nice", "Naples", "Copenhagen"],
    "Bucharest": ["Copenhagen", "Brussels", "Hamburg", "Naples", "Zurich"],
    "Venice": ["Brussels", "Naples", "Copenhagen", "Zurich", "Nice", "Hamburg"],
    "Nice": ["Zurich", "Hamburg", "Brussels", "Naples", "Venice", "Copenhagen"],
    "Hamburg": ["Nice", "Bucharest", "Brussels", "Zurich", "Copenhagen", "Venice", "Salzburg"],
    "Copenhagen": ["Bucharest", "Venice", "Naples", "Zurich", "Brussels", "Hamburg", "Nice"],
    "Naples": ["Zurich", "Venice", "Bucharest", "Brussels", "Copenhagen", "Nice", "Hamburg"],
    "Salzburg": ["Hamburg"]
}

# Create solver
s = Solver()

# Days 1-25
days = 25
day_city = [Int(f"day_{i}_city") for i in range(1, days + 1)]

# City to ID mapping
city_ids = {city: idx for idx, city in enumerate(cities.keys())}
id_to_city = {idx: city for city, idx in city_ids.items()}

# Each day must be assigned to a valid city
for dc in day_city:
    s.add(Or([dc == city_ids[city] for city in cities]))

# Days per city constraint
for city, req_days in cities.items():
    s.add(Sum([If(day_city[i] == city_ids[city], 1, 0) for i in range(days)]) == req_days)

# Specific constraints:
# Brussels between day 21-22
s.add(Or(day_city[20] == city_ids["Brussels"], day_city[21] == city_ids["Brussels"]))

# Copenhagen wedding (day 18-21)
s.add(Or([day_city[i] == city_ids["Copenhagen"] for i in range(17, 21)]))

# Nice relatives (day 9-11)
s.add(Or([day_city[i] == city_ids["Nice"] for i in range(8, 11)]))

# Naples workshop (day 22-25)
s.add(Or([day_city[i] == city_ids["Naples"] for i in range(21, 25)]))

# Flight connectivity
for i in range(days - 1):
    current = day_city[i]
    next_c = day_city[i + 1]
    s.add(Or(
        current == next_c,
        *[And(current == city_ids[c1], next_c == city_ids[c2]) 
          for c1 in cities for c2 in direct_flights.get(c1, [])]
    ))

# Solve and output
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(days):
        city_id = model.evaluate(day_city[i]).as_long()
        itinerary.append({"day": i + 1, "city": id_to_city[city_id]})
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid itinerary found.")