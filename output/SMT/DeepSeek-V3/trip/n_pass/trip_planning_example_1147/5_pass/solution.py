import json
from z3 import *

# Cities and their required days
cities = {
    "Brussels": 3,
    "Helsinki": 3,
    "Split": 4,
    "Dubrovnik": 2,
    "Istanbul": 5,
    "Milan": 4,
    "Vilnius": 5,
    "Frankfurt": 3
}

# Direct flights: represented as a set of tuples (from, to)
direct_flights = {
    ("Milan", "Frankfurt"), ("Split", "Frankfurt"), ("Milan", "Split"),
    ("Brussels", "Vilnius"), ("Brussels", "Helsinki"), ("Istanbul", "Brussels"),
    ("Milan", "Vilnius"), ("Brussels", "Milan"), ("Istanbul", "Helsinki"),
    ("Helsinki", "Vilnius"), ("Helsinki", "Dubrovnik"), ("Split", "Vilnius"),
    ("Dubrovnik", "Istanbul"), ("Istanbul", "Milan"), ("Helsinki", "Frankfurt"),
    ("Istanbul", "Vilnius"), ("Split", "Helsinki"), ("Milan", "Helsinki"),
    ("Istanbul", "Frankfurt"), ("Brussels", "Frankfurt"), ("Dubrovnik", "Frankfurt"),
    ("Frankfurt", "Vilnius")
}

# Make flights bidirectional
bidirectional_flights = set()
for (a, b) in direct_flights:
    bidirectional_flights.add((a, b))
    bidirectional_flights.add((b, a))
direct_flights = bidirectional_flights

# Create a Z3 solver
s = Solver()

# Create variables: for each day (1..22), which city are we in?
days = 22
city_vars = [Int(f"day_{i}") for i in range(1, days + 1)]

# Assign each city a unique integer
city_ids = {city: idx for idx, city in enumerate(cities.keys())}
id_to_city = {idx: city for city, idx in city_ids.items()}

# Constraints: each day's variable must be one of the city IDs
for day_var in city_vars:
    s.add(Or([day_var == city_ids[city] for city in cities]))

# Fixed events:
# Istanbul from day 1 to 5 (days 1, 2, 3, 4, 5)
for day in range(1, 6):
    s.add(city_vars[day - 1] == city_ids["Istanbul"])

# Vilnius between day 18 and 22 (days 18, 19, 20, 21, 22)
for day in range(18, 23):
    s.add(city_vars[day - 1] == city_ids["Vilnius"])

# Frankfurt between day 16 and 18 (days 16, 17, 18)
for day in range(16, 19):
    s.add(city_vars[day - 1] == city_ids["Frankfurt"])

# Constraints for transitions: adjacent days must be either the same city or connected by a direct flight
for i in range(days - 1):
    current_day_var = city_vars[i]
    next_day_var = city_vars[i + 1]
    # Either stay in the same city or move to a connected city
    s.add(Or(
        current_day_var == next_day_var,
        And(
            current_day_var != next_day_var,
            Or([And(current_day_var == city_ids[a], next_day_var == city_ids[b]) 
                for (a, b) in direct_flights if a in city_ids and b in city_ids])
        )
    ))

# Constraints for total days per city
for city, required_days in cities.items():
    city_id = city_ids[city]
    total_days = Sum([If(city_vars[i] == city_id, 1, 0) for i in range(days)])
    s.add(total_days == required_days)

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    itinerary = []
    for day in range(1, days + 1):
        city_id = model.evaluate(city_vars[day - 1]).as_long()
        city = id_to_city[city_id]
        itinerary.append({"day": day, "place": city})
    
    # Prepare the JSON output
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")