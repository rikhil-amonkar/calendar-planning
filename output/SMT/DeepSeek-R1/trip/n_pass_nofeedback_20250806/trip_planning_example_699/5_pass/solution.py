import json
from z3 import Solver, Bool, Sum, If, Or, And, Not

# Define cities and days
cities = ["Hamburg", "Dublin", "Reykjavik", "London", "Helsinki", "Mykonos"]
days = list(range(1, 17))

# Create solver and variables
s = Solver()
in_city = {c: [Bool(f'in_{c}_{d}') for d in days] for c in cities}

# Fixed events constraints
s.add(in_city["Hamburg"][0] == True)  # Day 1
s.add(in_city["Hamburg"][1] == True)  # Day 2
for d in range(1, 6):  # Days 2-6 (index 1-5)
    s.add(in_city["Dublin"][d] == True)
s.add(in_city["Reykjavik"][8] == True)  # Day 9 (index 8)
s.add(in_city["Reykjavik"][9] == True)  # Day 10 (index 9)

# Day 1 constraints (only Hamburg)
for city in ["Dublin", "Reykjavik", "London", "Helsinki", "Mykonos"]:
    s.add(in_city[city][0] == False)

# Day 2 constraints (only Hamburg and Dublin)
for city in ["Reykjavik", "London", "Helsinki", "Mykonos"]:
    s.add(in_city[city][1] == False)

# Total days per city
s.add(Sum([If(in_city["London"][d], 1, 0) for d in range(16)) == 5)
s.add(Sum([If(in_city["Helsinki"][d], 1, 0) for d in range(16)) == 4)
s.add(Sum([If(in_city["Mykonos"][d], 1, 0) for d in range(16)) == 3)

# Daily constraints: exactly 1-2 cities per day
for d in range(16):
    city_flags = [in_city[c][d] for c in cities]
    s.add(Or(city_flags))  # At least one city
    s.add(Sum([If(flag, 1, 0) for flag in city_flags]) <= 2)  # At most two cities

# Consecutive days must share at least one city
for d in range(15):  # Days 1-15 paired with next day
    s.add(Or([And(in_city[c][d], in_city[c][d+1]) for c in cities]))

# Flight connections constraints
allowed_pairs = {
    ("Dublin", "London"), ("Hamburg", "Dublin"), 
    ("Helsinki", "Reykjavik"), ("Hamburg", "London"),
    ("Dublin", "Helsinki"), ("Reykjavik", "London"),
    ("London", "Mykonos"), ("Dublin", "Reykjavik"),
    ("Hamburg", "Helsinki"), ("Helsinki", "London")
}

# Allow only direct flight pairs to be together on the same day
for d in range(16):
    for i in range(len(cities)):
        for j in range(i+1, len(cities)):
            c1, c2 = cities[i], cities[j]
            if (c1, c2) not in allowed_pairs and (c2, c1) not in allowed_pairs:
                s.add(Not(And(in_city[c1][d], in_city[c2][d])))

# Solve the model
if s.check() == sat:
    model = s.model()
    itinerary = []
    for d in range(16):
        day_cities = []
        for c in cities:
            if model.evaluate(in_city[c][d]):
                day_cities.append(c)
        # For single-city days, just add the city
        if len(day_cities) == 1:
            itinerary.append({"day": d+1, "city": day_cities[0]})
        # For two-city days (flight days), add both with flight indicator
        elif len(day_cities) == 2:
            itinerary.append({"day": d+1, "city": f"{day_cities[0]} to {day_cities[1]}"})
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"error": "No solution found"}))