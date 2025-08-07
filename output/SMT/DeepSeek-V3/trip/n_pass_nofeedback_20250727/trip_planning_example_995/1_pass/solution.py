import json
from z3 import *

# Define the cities
cities = {
    "Oslo": 0,
    "Stuttgart": 1,
    "Venice": 2,
    "Split": 3,
    "Barcelona": 4,
    "Brussels": 5,
    "Copenhagen": 6
}

# Inverse mapping for cities
city_names = {v: k for k, v in cities.items()}

# Direct flights as adjacency list
direct_flights_adj = {
    cities["Venice"]: [cities["Stuttgart"], cities["Barcelona"], cities["Brussels"], cities["Oslo"], cities["Copenhagen"]],
    cities["Stuttgart"]: [cities["Venice"], cities["Barcelona"], cities["Copenhagen"], cities["Split"]],
    cities["Oslo"]: [cities["Brussels"], cities["Split"], cities["Venice"], cities["Copenhagen"], cities["Barcelona"]],
    cities["Split"]: [cities["Copenhagen"], cities["Oslo"], cities["Stuttgart"], cities["Barcelona"]],
    cities["Barcelona"]: [cities["Copenhagen"], cities["Venice"], cities["Stuttgart"], cities["Split"], cities["Brussels"], cities["Oslo"]],
    cities["Brussels"]: [cities["Oslo"], cities["Venice"], cities["Copenhagen"], cities["Barcelona"]],
    cities["Copenhagen"]: [cities["Split"], cities["Barcelona"], cities["Brussels"], cities["Oslo"], cities["Venice"], cities["Stuttgart"]]
}

# Create Z3 variables for each day (1..16)
s = Solver()
day_city = [Int(f"day_{i}_city") for i in range(1, 17)]

# Each day's city must be one of the 7 cities
for day in day_city:
    s.add(Or([day == c for c in cities.values()]))

# Flight constraints: consecutive days must be the same city or connected by direct flight
for i in range(15):
    current_day = day_city[i]
    next_day = day_city[i+1]
    s.add(Or([
        And(current_day == c,
            Or([next_day == adj for adj in [c] + direct_flights_adj[c]])
        )
        for c in cities.values()
    ]))

# Duration constraints
# Oslo: 2 days
s.add(Sum([If(day == cities["Oslo"], 1, 0) for day in day_city]) == 2)
# Stuttgart: 3 days
s.add(Sum([If(day == cities["Stuttgart"], 1, 0) for day in day_city]) == 3)
# Venice: 4 days
s.add(Sum([If(day == cities["Venice"], 1, 0) for day in day_city]) == 4)
# Split: 4 days
s.add(Sum([If(day == cities["Split"], 1, 0) for day in day_city]) == 4)
# Barcelona: 3 days
s.add(Sum([If(day == cities["Barcelona"], 1, 0) for day in day_city]) == 3)
# Brussels: 3 days
s.add(Sum([If(day == cities["Brussels"], 1, 0) for day in day_city]) == 3)
# Copenhagen: 3 days
s.add(Sum([If(day == cities["Copenhagen"], 1, 0) for day in day_city]) == 3)

# Event constraints
# Barcelona from day 1 to 3 (days 1, 2, 3)
s.add(day_city[0] == cities["Barcelona"])
s.add(day_city[1] == cities["Barcelona"])
s.add(day_city[2] == cities["Barcelona"])

# Oslo between day 3 and day 4 (day 3 or day 4)
s.add(Or(
    day_city[2] == cities["Oslo"],  # day 3
    day_city[3] == cities["Oslo"]   # day 4
))

# Meet friend in Brussels between day 9 and 11 (days 9, 10, or 11)
s.add(Or(
    day_city[8] == cities["Brussels"],  # day 9
    day_city[9] == cities["Brussels"],  # day 10
    day_city[10] == cities["Brussels"]  # day 11
))

# Solve the problem
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(16):
        day = i + 1
        city_val = model.evaluate(day_city[i]).as_long()
        city_name = city_names[city_val]
        itinerary.append({"day": day, "place": city_name})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No valid itinerary found.")