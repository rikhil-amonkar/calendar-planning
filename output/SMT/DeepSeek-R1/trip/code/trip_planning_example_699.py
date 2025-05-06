from z3 import *

# Define cities and their IDs
cities = ["Mykonos", "Reykjavik", "Dublin", "London", "Helsinki", "Hamburg"]
city_id = {city: idx for idx, city in enumerate(cities)}

# Direct flights (bidirectional)
direct_flights = [
    ("Dublin", "London"),
    ("Hamburg", "Dublin"),
    ("Helsinki", "Reykjavik"),
    ("Hamburg", "London"),
    ("Dublin", "Helsinki"),
    ("Reykjavik", "London"),
    ("London", "Mykonos"),
    ("Dublin", "Reykjavik"),
    ("Hamburg", "Helsinki"),
    ("Helsinki", "London")
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
    city_id["Mykonos"]: 3,
    city_id["Reykjavik"]: 2,
    city_id["Dublin"]: 5,
    city_id["London"]: 5,
    city_id["Helsinki"]: 4,
    city_id["Hamburg"]: 2
}

# Create solver
s = Solver()

# Day variables: 0-based for 16 days (days 1-16)
days = [Int(f'day_{i+1}') for i in range(16)]
for day in days:
    s.add(day >= 0, day < 6)  # Validate city IDs (0-5)

# Sum constraints for each city
for city in required_days:
    total = Sum([If(day == city, 1, 0) for day in days])
    s.add(total == required_days[city])

# Flight constraints between consecutive days
for i in range(15):
    current = days[i]
    next_day = days[i+1]
    constraints = [current == next_day]  # Stay in same city
    for a, b in flight_pairs:
        constraints.append(And(current == a, next_day == b))
    s.add(Or(constraints))

# Specific constraints
dublin = city_id["Dublin"]
reykjavik = city_id["Reykjavik"]
hamburg = city_id["Hamburg"]

# Dublin must be days 2-6 (indices 1-5)
for i in range(1, 6):
    s.add(days[i] == dublin)

# Hamburg must be days 1-2 (indices 0-1)
s.add(days[0] == hamburg)
s.add(days[1] == hamburg)

# Reykjavik wedding between days 9-10 (indices 8-9)
s.add(days[8] == reykjavik)
s.add(days[9] == reykjavik)

# Check and print solution
if s.check() == sat:
    m = s.model()
    schedule = [m[day] for day in days]
    city_names = {v: k for k, v in city_id.items()}
    current_city = schedule[0]
    start_day = 1
    for i in range(1, 16):
        if schedule[i] != current_city:
            print(f"Days {start_day}-{i}: {city_names[current_city.as_long()]}")
            current_city = schedule[i]
            start_day = i + 1
    print(f"Days {start_day}-16: {city_names[current_city.as_long()]}")
else:
    print("No valid itinerary possible.")