import json
from z3 import *

# Define the cities and their required days
cities = {
    "Valencia": 2,
    "Oslo": 3,
    "Lyon": 4,
    "Prague": 3,
    "Paris": 4,
    "Nice": 4,
    "Seville": 5,
    "Tallinn": 2,
    "Mykonos": 5,
    "Lisbon": 2
}

# Direct flights as a set of tuples
direct_flights = {
    ("Lisbon", "Paris"),
    ("Lyon", "Nice"),
    ("Tallinn", "Oslo"),
    ("Prague", "Lyon"),
    ("Paris", "Oslo"),
    ("Lisbon", "Seville"),
    ("Prague", "Lisbon"),
    ("Oslo", "Nice"),
    ("Valencia", "Paris"),
    ("Valencia", "Lisbon"),
    ("Paris", "Nice"),
    ("Nice", "Mykonos"),
    ("Paris", "Lyon"),
    ("Valencia", "Lyon"),
    ("Prague", "Oslo"),
    ("Prague", "Paris"),
    ("Seville", "Paris"),
    ("Oslo", "Lyon"),
    ("Prague", "Valencia"),
    ("Lisbon", "Nice"),
    ("Lisbon", "Oslo"),
    ("Valencia", "Seville"),
    ("Lisbon", "Lyon"),
    ("Paris", "Tallinn"),
    ("Prague", "Tallinn")
}

# Ensure flights are bidirectional
bidirectional_flights = set()
for (a, b) in direct_flights:
    bidirectional_flights.add((a, b))
    bidirectional_flights.add((b, a))
direct_flights = bidirectional_flights

# Create Z3 solver
s = Solver()

# Variables: day_1 to day_25, each can be one of the cities
days = [Int(f"day_{i}") for i in range(1, 26)]

# Each day must be one of the cities
city_names = list(cities.keys())
city_ints = {city: i for i, city in enumerate(city_names)}
for day in days:
    s.add(Or([day == city_ints[city] for city in city_names]))

# Constraint: total days per city must match requirements
for city, required_days in cities.items():
    s.add(Sum([If(day == city_ints[city], 1, 0) for day in days]) == required_days)

# Specific constraints:
# Valencia between day 3 and day 4 (i.e., day 3 or 4 must include Valencia)
s.add(Or(days[2] == city_ints["Valencia"], days[3] == city_ints["Valencia"]))

# Oslo between day 13 and day 15 (i.e., one of days 13, 14, or 15 is Oslo)
s.add(Or([days[i] == city_ints["Oslo"] for i in range(12, 15)]))

# Seville between day 5 and day 9 (i.e., days 5-9 must include Seville for the show)
s.add(Or([days[i] == city_ints["Seville"] for i in range(4, 9)]))

# Mykonos between day 21 and day 25 (wedding)
s.add(Or([days[i] == city_ints["Mykonos"] for i in range(20, 25)]))

# Flight constraints: consecutive days must be same city or have a direct flight
for i in range(24):
    current_day = days[i]
    next_day = days[i+1]
    # Either same city or direct flight
    s.add(Or(
        current_day == next_day,
        *[
            And(current_day == city_ints[a], next_day == city_ints[b])
            for (a, b) in direct_flights
        ]
    ))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(1, 26):
        day_val = model.eval(days[i-1]).as_long()
        city = city_names[day_val]
        itinerary.append({"day": i, "place": city})
    
    # Verify all constraints are met (sanity check)
    # Prepare the output
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")