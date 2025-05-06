from z3 import *

# Define cities and their IDs
cities = ["Paris", "Florence", "Vienna", "Porto", "Munich", "Nice", "Warsaw"]
city_id = {city: idx for idx, city in enumerate(cities)}

# Direct flights (handle one-way 'from Florence to Munich')
direct_flights = [
    ("Florence", "Vienna"),
    ("Paris", "Warsaw"),
    ("Munich", "Vienna"),
    ("Porto", "Vienna"),
    ("Warsaw", "Vienna"),
    ("Florence", "Munich"),  # One-way
    ("Munich", "Warsaw"),
    ("Munich", "Nice"),
    ("Paris", "Florence"),
    ("Warsaw", "Nice"),
    ("Porto", "Munich"),
    ("Porto", "Nice"),
    ("Paris", "Vienna"),
    ("Nice", "Vienna"),
    ("Porto", "Paris"),
    ("Paris", "Nice"),
    ("Paris", "Munich"),
    ("Porto", "Warsaw")
]

# Create flight pairs (bidirectional except for one-way Florence->Munich)
flight_pairs = []
for a, b in direct_flights:
    a_id = city_id[a]
    b_id = city_id[b]
    flight_pairs.append((a_id, b_id))
    if (a, b) != ("Florence", "Munich"):  # Add reverse except for one-way
        flight_pairs.append((b_id, a_id))

# Required days per city
required_days = {
    city_id["Paris"]: 5,
    city_id["Florence"]: 3,
    city_id["Vienna"]: 2,
    city_id["Porto"]: 3,
    city_id["Munich"]: 5,
    city_id["Nice"]: 5,
    city_id["Warsaw"]: 3
}

# Create solver
s = Solver()

# Day variables: 20 days (indices 0-19 correspond to days 1-20)
days = [Int(f'day_{i+1}') for i in range(20)]
for day in days:
    s.add(day >= 0, day < 7)  # Validate city IDs (0-6)

# Sum constraints for each city
for city in required_days:
    total = Sum([If(day == city, 1, 0) for day in days])
    s.add(total == required_days[city])

# Flight constraints between consecutive days
for i in range(19):
    current = days[i]
    next_day = days[i+1]
    constraints = [current == next_day]  # Stay in same city
    for a, b in flight_pairs:
        constraints.append(And(current == a, next_day == b))
    s.add(Or(constraints))

# Specific date constraints
porto = city_id["Porto"]
vienna = city_id["Vienna"]
warsaw = city_id["Warsaw"]

# Porto must be days 1-3 (indices 0-2)
for i in range(0, 3):
    s.add(days[i] == porto)

# Vienna must be days 19-20 (indices 18-19)
s.add(days[18] == vienna)
s.add(days[19] == vienna)

# Warsaw must be days 13-15 (indices 12-14)
for i in range(12, 15):
    s.add(days[i] == warsaw)

# Check and print solution
if s.check() == sat:
    m = s.model()
    schedule = [m[day] for day in days]
    city_names = {v: k for k, v in city_id.items()}
    current_city = schedule[0]
    start_day = 1
    for i in range(1, 20):
        if schedule[i] != current_city:
            print(f"Days {start_day}-{i}: {city_names[current_city.as_long()]}")
            current_city = schedule[i]
            start_day = i + 1
    print(f"Days {start_day}-20: {city_names[current_city.as_long()]}")
else:
    print("No valid itinerary possible.")