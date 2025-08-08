import z3

cities = ["Brussels", "Venice", "Santorini", "Lisbon", "Reykjavik", "London", "Madrid"]
city_to_int = {city: idx for idx, city in enumerate(cities)}
int_to_city = {idx: city for idx, city in enumerate(cities)}

# Flight connections setup
directed_flights = []
bidirectional = [
    ("Venice", "Madrid"), ("Lisbon", "Reykjavik"), ("Brussels", "Venice"),
    ("Venice", "Santorini"), ("Lisbon", "Venice"), ("Brussels", "London"),
    ("Madrid", "London"), ("Santorini", "London"), ("London", "Reykjavik"),
    ("Brussels", "Lisbon"), ("Lisbon", "London"), ("Lisbon", "Madrid"),
    ("Madrid", "Santorini"), ("Brussels", "Reykjavik"), ("Brussels", "Madrid"),
    ("Venice", "London")
]

for a, b in bidirectional:
    a_int, b_int = city_to_int[a], city_to_int[b]
    directed_flights.append((a_int, b_int))
    directed_flights.append((b_int, a_int))
directed_flights.append((city_to_int["Reykjavik"], city_to_int["Madrid"]))

# Duration constraints
total_days = {
    city_to_int["Brussels"]: 2,
    city_to_int["Venice"]: 3,
    city_to_int["Santorini"]: 3,
    city_to_int["Lisbon"]: 4,
    city_to_int["Reykjavik"]: 3,
    city_to_int["London"]: 3,
    city_to_int["Madrid"]: 5
}

solver = z3.Solver()
c = [z3.Int(f"c_{i}") for i in range(17)]  # End city for each day

# City-day presence tracking
in_city = [[z3.Bool(f"in_{i}_{j}") for j in range(7)] for i in range(17)]

# Initialize day 0 starting in Brussels
solver.add(c[0] == city_to_int["Brussels"])

# Conference in Brussels on days 1-2
solver.add(c[0] == city_to_int["Brussels"])
solver.add(c[1] == city_to_int["Brussels"])

# Wedding in Madrid on days 7-11
for day in range(6, 11):  # Days 7-11 (0-indexed days 6-10)
    solver.add(z3.Or(c[day] == city_to_int["Madrid"], c[day-1] == city_to_int["Madrid"]))

# Visit Venice between days 5-7
venice_visit = z3.Bool("venice_visit")
solver.add(z3.Or(
    c[4] == city_to_int["Venice"],  # Day 5
    c[5] == city_to_int["Venice"],  # Day 6
    c[6] == city_to_int["Venice"]   # Day 7
))

# City presence constraints
for day in range(17):
    # Valid city range
    solver.add(c[day] >= 0, c[day] < 7)
    
    # Start city: previous end city or Brussels for day 0
    start_city = c[day-1] if day > 0 else city_to_int["Brussels"]
    
    # Flight constraints
    solver.add(z3.Or(
        start_city == c[day],  # Stay in same city
        z3.Or([z3.And(start_city == a, c[day] == b) for a, b in directed_flights])  # Valid flight
    ))
    
    # Define city-day presence
    for city_idx in range(7):
        solver.add(
            in_city[day][city_idx] == z3.Or(start_city == city_idx, c[day] == city_idx)
        )

# Total days per city
for city_idx, days_required in total_days.items():
    solver.add(z3.Sum([z3.If(in_city[day][city_idx], 1, 0) for day in range(17)]) == days_required)

# Solve and output
if solver.check() == z3.sat:
    model = solver.model()
    itinerary = []
    for i in range(17):
        city_code = model.evaluate(c[i]).as_long()
        itinerary.append({"day": i+1, "place": int_to_city[city_code]})
    print({"itinerary": itinerary})
else:
    print("No solution found")