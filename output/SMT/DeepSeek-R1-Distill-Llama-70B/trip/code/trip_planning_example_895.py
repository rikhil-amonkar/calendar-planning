import z3

# Define cities and their IDs
cities = ['Venice', 'London', 'Lisbon', 'Brussels', 'Reykjavik', 'Santorini', 'Madrid']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [6, 1, 3, 2],    # Venice can fly to Madrid (6), London (1), Brussels (3), Lisbon (2)
    1: [0, 6, 4, 2, 3], # London can fly to Venice (0), Madrid (6), Reykjavik (4), Lisbon (2), Brussels (3)
    2: [0, 1, 3, 4, 6], # Lisbon can fly to Venice (0), London (1), Brussels (3), Reykjavik (4), Madrid (6)
    3: [0, 1, 2, 4, 6], # Brussels can fly to Venice (0), London (1), Lisbon (2), Reykjavik (4), Madrid (6)
    4: [1, 2, 3, 6],     # Reykjavik can fly to London (1), Lisbon (2), Brussels (3), Madrid (6)
    5: [1, 6],           # Santorini can fly to London (1), Madrid (6)
    6: [0, 1, 2, 3, 4, 5] # Madrid can fly to Venice (0), London (1), Lisbon (2), Brussels (3), Reykjavik (4), Santorini (5)
}

# Create variables for each day (1 to 17)
days = [z3.Int(f'd_{i}') for i in range(1, 18)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-6)
for d in days:
    s.add(z3.And(d >= 0, d < 7))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 3)  # Venice
s.add(z3.Count(1, days) == 3)  # London
s.add(z3.Count(2, days) == 4)  # Lisbon
s.add(z3.Count(3, days) == 2)  # Brussels
s.add(z3.Count(4, days) == 3)  # Reykjavik
s.add(z3.Count(5, days) == 3)  # Santorini
s.add(z3.Count(6, days) == 5)  # Madrid

# Add event constraints
# Days 1 and 2 must be in Brussels (indices 0 and 1)
s.add(days[0] == 3)
s.add(days[1] == 3)
# Days 5 to 7 must be in Venice (indices 4 to 6)
for i in range(4, 7):
    s.add(days[i] == 0)
# Days 7 to 11 must be in Madrid (indices 6 to 10)
for i in range(6, 11):
    s.add(days[i] == 6)

# Add transition constraints between consecutive days
for i in range(17):
    current_day = days[i]
    next_day = days[i+1] if i < 16 else None
    if i < 16:
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