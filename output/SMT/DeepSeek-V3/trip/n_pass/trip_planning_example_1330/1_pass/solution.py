import json
from z3 import *

# Define the cities and their required days
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

# Direct flights between cities
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

# Create a solver instance
s = Solver()

# Days are 1..25
days = 25
day_city = [Int(f"day_{i}_city") for i in range(1, days+1)]

# City to integer mapping
city_ids = {city: idx for idx, city in enumerate(cities.keys())}
id_to_city = {idx: city for city, idx in city_ids.items()}

# Constraint: Each day_city variable must be one of the city IDs
for dc in day_city:
    s.add(Or([dc == city_ids[city] for city in cities]))

# Constraints for required days per city
for city, required_days in cities.items():
    s.add(Sum([If(day_city[i] == city_ids[city], 1, 0) for i in range(days)]) == required_days)

# Specific constraints:
# Brussels: must be there between day 21 and 22 (so either day 21 or 22)
s.add(Or(day_city[20] == city_ids["Brussels"], day_city[21] == city_ids["Brussels"]))  # days are 1-based; 21 is index 20, 22 is 21

# Copenhagen: wedding between day 18-21 (so at least one of days 18,19,20,21)
s.add(Or([day_city[i] == city_ids["Copenhagen"] for i in range(17, 21)]))  # 18 is 17, 21 is 20

# Nice: relatives between day 9-11 (so at least one of days 9,10,11)
s.add(Or([day_city[i] == city_ids["Nice"] for i in range(8, 11)]))  # 9 is 8, 11 is 10

# Naples: workshop between day 22-25 (so at least one of days 22,23,24,25)
s.add(Or([day_city[i] == city_ids["Naples"] for i in range(21, 25)]))  # 22 is 21, 25 is 24

# Flight constraints: consecutive days must be same city or have a direct flight
for i in range(days - 1):
    current_city = day_city[i]
    next_city = day_city[i+1]
    # Either stay in the same city or move to a directly connected city
    s.add(Or(
        current_city == next_city,
        *[And(current_city == city_ids[city1], next_city == city_ids[city2]) 
          for city1 in cities for city2 in direct_flights.get(city1, [])]
    ))

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(days):
        city_id = model.evaluate(day_city[i]).as_long()
        city = id_to_city[city_id]
        itinerary.append({"day": i+1, "city": city})
    
    # Prepare the output
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No valid itinerary found.")