from z3 import *

# Define cities and their IDs
cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
city_id = {city: idx for idx, city in enumerate(cities)}

# Direct flights (bidirectional)
direct_flights = [
    ("Riga", "Oslo"),
    ("Rome", "Oslo"),
    ("Vienna", "Milan"),
    ("Vienna", "Vilnius"),
    ("Vienna", "Lisbon"),
    ("Riga", "Milan"),
    ("Lisbon", "Oslo"),
    ("Rome", "Riga"),
    ("Rome", "Lisbon"),
    ("Vienna", "Riga"),
    ("Vienna", "Rome"),
    ("Milan", "Oslo"),
    ("Vienna", "Oslo"),
    ("Vilnius", "Oslo"),
    ("Riga", "Vilnius"),
    ("Vilnius", "Milan"),
    ("Riga", "Lisbon"),
    ("Milan", "Lisbon")
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
    city_id["Vienna"]: 4,
    city_id["Milan"]: 2,
    city_id["Rome"]: 3,
    city_id["Riga"]: 2,
    city_id["Lisbon"]: 3,
    city_id["Vilnius"]: 4,
    city_id["Oslo"]: 3
}

# Create solver
s = Solver()

# Day variables: 15 days (indices 0-14 correspond to days 1-15)
days = [Int(f'day_{i+1}') for i in range(15)]
for day in days:
    s.add(day >= 0, day < 7)  # Validate city IDs (0-6)

# Sum constraints for each city
for city in required_days:
    total = Sum([If(day == city, 1, 0) for day in days])
    s.add(total == required_days[city])

# Flight constraints between consecutive days
for i in range(14):
    current = days[i]
    next_day = days[i+1]
    constraints = [current == next_day]  # Stay in same city
    for a, b in flight_pairs:
        constraints.append(And(current == a, next_day == b))
    s.add(Or(constraints))

# Specific date constraints
vienna = city_id["Vienna"]
lisbon = city_id["Lisbon"]
oslo = city_id["Oslo"]

# Vienna must be days 1-4 (indices 0-3)
for i in range(0, 4):
    s.add(days[i] == vienna)

# Lisbon must be days 11-13 (indices 10-12)
for i in range(10, 13):
    s.add(days[i] == lisbon)

# Oslo must be days 13-15 (indices 12-14)
for i in range(12, 15):
    s.add(days[i] == oslo)

# Check and print solution
if s.check() == sat:
    m = s.model()
    schedule = [m[day] for day in days]
    city_names = {v: k for k, v in city_id.items()}
    current_city = schedule[0]
    start_day = 1
    for i in range(1, 15):
        if schedule[i] != current_city:
            print(f"Days {start_day}-{i}: {city_names[current_city.as_long()]}")
            current_city = schedule[i]
            start_day = i + 1
    print(f"Days {start_day}-15: {city_names[current_city.as_long()]}")
else:
    print("No valid itinerary possible.")