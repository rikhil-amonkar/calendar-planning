from z3 import *

# Define cities and their IDs
cities = ["Naples", "Seville", "Milan"]
city_id = {city: idx for idx, city in enumerate(cities)}

# Direct flights (bidirectional)
direct_flights = [
    ("Milan", "Seville"),
    ("Naples", "Milan")
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
    city_id["Naples"]: 3,
    city_id["Seville"]: 4,
    city_id["Milan"]: 7
}

# Create solver
s = Solver()

# Day variables: 0-based for 12 days (days 1-12)
days = [Int(f'day_{i+1}') for i in range(12)]
for day in days:
    s.add(day >= 0, day < 3)  # City IDs 0 (Naples), 1 (Seville), 2 (Milan)

# Sum constraints for each city
for city in required_days:
    total = Sum([If(day == city, 1, 0) for day in days])
    s.add(total == required_days[city])

# Flight constraints between consecutive days
for i in range(11):
    current = days[i]
    next_day = days[i+1]
    # Either stay in the same city or fly directly
    constraints = [current == next_day]
    for a, b in flight_pairs:
        constraints.append(And(current == a, next_day == b))
    s.add(Or(constraints))

# Specific constraint: Seville from day 9 to 12 (indices 8 to 11)
seville = city_id["Seville"]
for i in range(8, 12):
    s.add(days[i] == seville)

# Check and print solution
if s.check() == sat:
    m = s.model()
    schedule = [m[day] for day in days]
    city_names = {v: k for k, v in city_id.items()}
    current_city = schedule[0]
    start_day = 1
    for i in range(1, 12):
        if schedule[i] != current_city:
            print(f"Days {start_day}-{i}: {city_names[current_city.as_long()]}")
            current_city = schedule[i]
            start_day = i + 1
    print(f"Days {start_day}-12: {city_names[current_city.as_long()]}")
else:
    print("No valid itinerary possible.")