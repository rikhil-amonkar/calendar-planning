import json
from z3 import *

# Cities and their required days
cities = {
    "Reykjavik": 2,
    "Stockholm": 2,
    "Porto": 5,
    "Nice": 3,
    "Venice": 4,
    "Vienna": 3,
    "Split": 3,
    "Copenhagen": 2
}

# Direct flights as a set of tuples
direct_flights = {
    ("Copenhagen", "Vienna"),
    ("Nice", "Stockholm"),
    ("Split", "Copenhagen"),
    ("Nice", "Reykjavik"),
    ("Nice", "Porto"),
    ("Reykjavik", "Vienna"),
    ("Stockholm", "Copenhagen"),
    ("Nice", "Venice"),
    ("Nice", "Vienna"),
    ("Reykjavik", "Copenhagen"),
    ("Nice", "Copenhagen"),
    ("Stockholm", "Vienna"),
    ("Venice", "Vienna"),
    ("Copenhagen", "Porto"),
    ("Reykjavik", "Stockholm"),
    ("Stockholm", "Split"),
    ("Split", "Vienna"),
    ("Copenhagen", "Venice"),
    ("Vienna", "Porto")
}

# Ensure flights are bidirectional
bidirectional_flights = set()
for (a, b) in direct_flights:
    bidirectional_flights.add((a, b))
    bidirectional_flights.add((b, a))
direct_flights = bidirectional_flights

# Create a mapping from city names to integers
city_ids = {city: i for i, city in enumerate(cities.keys())}
id_to_city = {i: city for city, i in city_ids.items()}

# Initialize Z3 solver
s = Solver()

# Variables: day[i] represents the city on day i+1 (days are 1-based)
days = [Int(f"day_{i}") for i in range(17)]

# Constraint: each day's city must be one of the 8 cities
for day in days:
    s.add(Or([day == city_ids[city] for city in cities]))

# Constraint: total days per city must match requirements
for city in cities:
    s.add(Sum([If(day == city_ids[city], 1, 0) for day in days]) == cities[city])

# Constraint: flights between consecutive days must be direct flights
for i in range(16):
    current_day = days[i]
    next_day = days[i+1]
    # Either same city or a direct flight exists
    s.add(Or(
        current_day == next_day,
        Or([And(current_day == city_ids[a], next_day == city_ids[b]) 
            for (a, b) in direct_flights if a in city_ids and b in city_ids])
    ))

# Reykjavik constraints: 2 days, and must be between day 3 and 4 (i.e., includes day 3 or 4)
s.add(Or(
    days[2] == city_ids["Reykjavik"],  # day 3 is index 2
    days[3] == city_ids["Reykjavik"]   # day 4 is index 3
))

# Stockholm constraints: 2 days, meet friends between day 4 and 5 (so includes day 4 or 5)
s.add(Or(
    days[3] == city_ids["Stockholm"],  # day 4
    days[4] == city_ids["Stockholm"]   # day 5
))

# Porto constraints: 5 days, wedding between day 13 and 17 (must include at least one day in 13-17)
s.add(Or([days[i] == city_ids["Porto"] for i in range(12, 17)]))

# Vienna constraints: 3 days, workshop between day 11 and 13 (must include at least one day in 11-13)
s.add(Or([days[i] == city_ids["Vienna"] for i in range(10, 13)]))

# Additional constraints to ensure the stays are continuous where possible
# For example, if a city is visited for multiple days, they should be consecutive
# This is a soft constraint to help the solver find a solution more easily
for city in cities:
    if cities[city] > 1:
        # At least one block of consecutive days equal to the required duration
        s.add(Or([
            And([days[i + j] == city_ids[city] for j in range(cities[city]))
            for i in range(17 - cities[city] + 1)
        ]))

# Check and get model
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(17):
        city_id = m.eval(days[i]).as_long()
        city_name = id_to_city[city_id]
        itinerary.append({"day": i+1, "place": city_name})
    
    # Verify constraints are met
    # (Additional checks can be added here)
    
    # Output as JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No valid itinerary found.")