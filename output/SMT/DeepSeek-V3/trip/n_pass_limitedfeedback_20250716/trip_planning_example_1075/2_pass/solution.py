import json
from z3 import *

# Define the cities and their required days
cities = {
    "Vienna": 4,
    "Lyon": 3,
    "Edinburgh": 4,
    "Reykjavik": 5,
    "Stuttgart": 5,
    "Manchester": 2,
    "Split": 5,
    "Prague": 4
}

# Direct flights as per the problem statement
direct_flights = {
    "Reykjavik": ["Stuttgart", "Vienna", "Prague"],
    "Stuttgart": ["Split", "Vienna", "Edinburgh", "Manchester"],
    "Prague": ["Manchester", "Edinburgh", "Vienna", "Split", "Lyon"],
    "Manchester": ["Split", "Prague", "Vienna"],
    "Edinburgh": ["Prague", "Stuttgart"],
    "Vienna": ["Manchester", "Prague", "Lyon", "Split", "Stuttgart", "Reykjavik"],
    "Split": ["Lyon", "Manchester", "Prague", "Stuttgart", "Vienna"],
    "Lyon": ["Vienna", "Split", "Prague"]
}

# Create all possible flight pairs (bidirectional)
flight_pairs = set()
for src, dests in direct_flights.items():
    for dest in dests:
        flight_pairs.add((src, dest))
        flight_pairs.add((dest, src))

# Initialize Z3 solver
s = Solver()

# Create Z3 constants for each city
City = Datatype('City')
for city in cities.keys():
    City.declare(city)
City = City.create()
city_consts = {city: getattr(City, city) for city in cities.keys()}

# Define a Flight function to check if a flight exists between two cities
def Flight(c1, c2):
    return Or([And(c1 == city_consts[src], c2 == city_consts[dest]) for src, dest in flight_pairs])

# Variables for each day:
# city_before[day] and city_after[day] represent the cities before and after potential flight on that day
city_before = [Const(f'city_before_{i}', City) for i in range(1, 26)]
city_after = [Const(f'city_after_{i}', City) for i in range(1, 26)]
is_travel_day = [Bool(f'travel_{i}') for i in range(1, 26)]

# Constraints:
# 1. If it's not a travel day, city_before equals city_after
for i in range(25):
    s.add(Implies(Not(is_travel_day[i]), city_before[i] == city_after[i]))

# 2. If it's a travel day, there must be a flight between city_before and city_after
for i in range(25):
    s.add(Implies(is_travel_day[i], Flight(city_before[i], city_after[i])))

# 3. Consecutive days must connect: city_after[i] == city_before[i+1]
for i in range(24):
    s.add(city_after[i] == city_before[i+1])

# 4. Total days per city must match requirements
for city, required_days in cities.items():
    total_days = 0
    for i in range(25):
        # The city is present on day i+1 if it's city_before or city_after
        total_days += If(Or(city_before[i] == city_consts[city], city_after[i] == city_consts[city]), 1, 0)
    s.add(total_days == required_days)

# 5. Fixed events:
# Edinburgh from day 5 to day 8 (1-based days 5-8)
for day in [4, 5, 6, 7]:  # 0-based indices for days 5-8
    s.add(Or(city_before[day] == city_consts["Edinburgh"], city_after[day] == city_consts["Edinburgh"]))

# Split between day 19 and 23 (1-based days 19-23, 0-based 18-22)
split_days = []
for day in range(18, 23):
    split_days.append(Or(city_before[day] == city_consts["Split"], city_after[day] == city_consts["Split"]))
s.add(Or(*split_days))

# Solve the model
if s.check() == sat:
    m = s.model()
    itinerary = []
    for day in range(1, 26):
        i = day - 1
        # Determine the cities for this day
        current_cities = set()
        for city in cities.keys():
            if m.evaluate(city_before[i] == city_consts[city]):
                current_cities.add(city)
            if m.evaluate(city_after[i] == city_consts[city]):
                current_cities.add(city)
        for city in current_cities:
            itinerary.append({"day": day, "place": city})
    
    # Prepare the output
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No valid itinerary found.")