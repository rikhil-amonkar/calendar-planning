import z3

# Define cities and their IDs
cities = ['Valencia', 'Riga', 'Prague', 'Mykonos', 'Zurich', 'Bucharest', 'Nice']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [5, 6],        # Valencia can fly to Bucharest (5) and Nice (6)
    1: [5, 6, 3],     # Riga can fly to Bucharest (5), Nice (6), and Mykonos (3)
    2: [4, 5, 1, 0],  # Prague can fly to Zurich (4), Bucharest (5), Riga (1), and Valencia (0)
    3: [0, 4, 6],     # Mykonos can fly to Valencia (0), Zurich (4), and Nice (6)
    4: [2, 3, 1, 5, 0, 6],  # Zurich can fly to Prague (2), Mykonos (3), Riga (1), Bucharest (5), Valencia (0), and Nice (6)
    5: [0, 1, 4, 3],  # Bucharest can fly to Valencia (0), Riga (1), Zurich (4), and Mykonos (3)
    6: [3, 4, 1]      # Nice can fly to Mykonos (3), Zurich (4), and Riga (1)
}

# Create variables for each day (1 to 22)
days = [z3.Int(f'd_{i}') for i in range(1, 23)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-6)
for d in days:
    s.add(z3.And(d >= 0, d < 7))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 5)  # Valencia
s.add(z3.Count(1, days) == 5)  # Riga
s.add(z3.Count(2, days) == 3)  # Prague
s.add(z3.Count(3, days) == 3)  # Mykonos
s.add(z3.Count(4, days) == 5)  # Zurich
s.add(z3.Count(5, days) == 5)  # Bucharest
s.add(z3.Count(6, days) == 2)  # Nice

# Add event constraints
# Days 1-3 must be in Mykonos (indices 0-2)
for i in range(3):
    s.add(days[i] == 3)
# Days 7-9 must be in Prague (indices 6-8)
for i in range(6, 9):
    s.add(days[i] == 2)

# Add transition constraints between consecutive days
for i in range(22):
    current_day = days[i]
    next_day = days[i+1] if i < 21 else None
    if i < 21:
        for a in range(7):
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