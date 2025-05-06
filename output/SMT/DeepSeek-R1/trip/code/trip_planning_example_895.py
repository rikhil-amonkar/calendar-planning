from z3 import *

# Define cities and their IDs
cities = ["Brussels", "Venice", "Lisbon", "London", "Reykjavik", "Santorini", "Madrid"]
city_id = {city: idx for idx, city in enumerate(cities)}

# Direct flights (bidirectional)
direct_flights = [
    ("Venice", "Madrid"),
    ("Lisbon", "Reykjavik"),
    ("Brussels", "Venice"),
    ("Venice", "Santorini"),
    ("Lisbon", "Venice"),
    ("Reykjavik", "Madrid"),
    ("Brussels", "London"),
    ("Madrid", "London"),
    ("Santorini", "London"),
    ("London", "Reykjavik"),
    ("Brussels", "Lisbon"),
    ("Lisbon", "London"),
    ("Lisbon", "Madrid"),
    ("Madrid", "Santorini"),
    ("Brussels", "Reykjavik"),
    ("Brussels", "Madrid"),
    ("Venice", "London")
]

# Create flight pairs in both directions
flight_pairs = []
for a, b in direct_flights:
    a_id = city_id[a]
    b_id = city_id[b]
    flight_pairs.append((a_id, b_id))
    flight_pairs.append((b_id, a_id))

# Required days per city
required_days = {
    city_id["Brussels"]: 2,
    city_id["Venice"]: 3,
    city_id["Lisbon"]: 4,
    city_id["London"]: 3,
    city_id["Reykjavik"]: 3,
    city_id["Santorini"]: 3,
    city_id["Madrid"]: 5
}

# Create solver
s = Solver()

# Day variables: 17 days (indices 0-16 correspond to days 1-17)
days = [Int(f'day_{i+1}') for i in range(17)]
for day in days:
    s.add(day >= 0, day < 7)  # Validate city IDs (0-6)

# Sum constraints for each city
for city in required_days:
    total = Sum([If(day == city, 1, 0) for day in days])
    s.add(total == required_days[city])

# Flight constraints between consecutive days
for i in range(16):
    current = days[i]
    next_day = days[i+1]
    constraints = [current == next_day]  # Stay in same city
    for a, b in flight_pairs:
        constraints.append(And(current == a, next_day == b))
    s.add(Or(constraints))

# Specific date constraints
brussels = city_id["Brussels"]
venice = city_id["Venice"]
madrid = city_id["Madrid"]

# Brussels must be days 1-2 (indices 0-1)
s.add(days[0] == brussels)
s.add(days[1] == brussels)

# Venice must be days 5-7 (indices 4-6)
for i in range(4, 7):
    s.add(days[i] == venice)

# Madrid must be days 7-11 (indices 6-10)
for i in range(6, 11):
    s.add(days[i] == madrid)

# Check and print solution
if s.check() == sat:
    m = s.model()
    schedule = [m[day] for day in days]
    city_names = {v: k for k, v in city_id.items()}
    current_city = schedule[0]
    start_day = 1
    for i in range(1, 17):
        if schedule[i] != current_city:
            print(f"Days {start_day}-{i}: {city_names[current_city.as_long()]}")
            current_city = schedule[i]
            start_day = i + 1
    print(f"Days {start_day}-17: {city_names[current_city.as_long()]}")
else:
    print("No valid itinerary possible.")