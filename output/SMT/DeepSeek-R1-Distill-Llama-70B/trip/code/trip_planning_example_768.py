import z3

# Define cities and their IDs
cities = ['Mykonos', 'Nice', 'London', 'Copenhagen', 'Oslo', 'Tallinn']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [2, 3],     # Mykonos can fly to London (2) and Nice (3)
    1: [2, 3, 4],  # Nice can fly to London (2), Mykonos (0), Oslo (4)
    2: [0, 1, 3, 4],  # London can fly to Mykonos (0), Nice (1), Copenhagen (3), Oslo (4)
    3: [2, 4, 5],  # Copenhagen can fly to London (2), Oslo (4), Tallinn (5)
    4: [1, 2, 3, 5],  # Oslo can fly to Nice (1), London (2), Copenhagen (3), Tallinn (5)
    5: [3, 4]      # Tallinn can fly to Copenhagen (3) and Oslo (4)
}

# Create variables for each day (1 to 16)
days = [z3.Int(f'd_{i}') for i in range(1, 17)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-5)
for d in days:
    s.add(z3.And(d >= 0, d < 6))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 4)  # Mykonos
s.add(z3.Count(1, days) == 3)  # Nice
s.add(z3.Count(2, days) == 2)  # London
s.add(z3.Count(3, days) == 3)  # Copenhagen
s.add(z3.Count(4, days) == 5)  # Oslo
s.add(z3.Count(5, days) == 4)  # Tallinn

# Add event constraints
# Days 14 and 16 must be in Nice (indices 13 and 15)
s.add(days[13] == 1)
s.add(days[15] == 1)
# Days 10 to 14 must be in Oslo (indices 9 to 13)
for i in range(9, 14):
    s.add(days[i] == 4)

# Add transition constraints between consecutive days
for i in range(16):
    current_day = days[i]
    next_day = days[i+1] if i < 15 else None
    if i < 15:
        for a in range(6):
            s.add(z3.Implies(current_day == a,
                              z3.Or([next_day == a] + [next_day == b for b in adj[a]])))

# Solve the model
result = s.check()
if result == z3.sat:
    model = s.model()
    schedule = [model[day].as_long() for day in days]
    city_schedule = [cities[idx] for idx in schedule]
    for i, city in enumerate(city_schedule, 1):
        print(f"Day {i}: {city}")
else:
    print("No solution exists due to conflicting constraints.")