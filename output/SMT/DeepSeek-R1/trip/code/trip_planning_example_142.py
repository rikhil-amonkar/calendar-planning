from z3 import *

# Define cities and their IDs
cities = ["Madrid", "Dublin", "Tallinn"]
city_id = {city: idx for idx, city in enumerate(cities)}

# Direct flights (bidirectional)
direct_flights = [
    ("Madrid", "Dublin"),
    ("Dublin", "Tallinn")
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
    city_id["Madrid"]: 4,
    city_id["Dublin"]: 3,
    city_id["Tallinn"]: 2
}

# Create solver
s = Solver()

# Day variables: 7 days (indices 0-6 correspond to days 1-7)
days = [Int(f'day_{i+1}') for i in range(7)]
for day in days:
    s.add(day >= 0, day < 3)  # Validate city IDs (0-2)

# Sum constraints for each city
for city in required_days:
    total = Sum([If(day == city, 1, 0) for day in days])
    s.add(total == required_days[city])

# Flight constraints between consecutive days
for i in range(6):
    current = days[i]
    next_day = days[i+1]
    constraints = [current == next_day]  # Stay in same city
    for a, b in flight_pairs:
        constraints.append(And(current == a, next_day == b))
    s.add(Or(constraints))

# Tallinn must be days 6-7 (indices 5-6)
tallinn = city_id["Tallinn"]
s.add(days[5] == tallinn)
s.add(days[6] == tallinn)

# Check and print solution
if s.check() == sat:
    m = s.model()
    schedule = [m[day] for day in days]
    city_names = {v: k for k, v in city_id.items()}
    current_city = schedule[0]
    start_day = 1
    for i in range(1, 7):
        if schedule[i] != current_city:
            print(f"Days {start_day}-{i}: {city_names[current_city.as_long()]}")
            current_city = schedule[i]
            start_day = i + 1
    print(f"Days {start_day}-7: {city_names[current_city.as_long()]}")
else:
    print("No valid itinerary possible.")