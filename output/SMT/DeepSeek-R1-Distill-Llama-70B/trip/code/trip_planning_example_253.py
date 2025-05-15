import z3

# Define cities and their IDs
cities = ['Amsterdam', 'Vienna', 'Santorini', 'Lyon']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1, 2, 3],  # Amsterdam can fly to Vienna, Santorini, Lyon
    1: [0, 2, 3],  # Vienna can fly to Amsterdam, Santorini, Lyon
    2: [0, 1, 3],  # Santorini can fly to Amsterdam, Vienna, Lyon
    3: [0, 1, 2],  # Lyon can fly to Amsterdam, Vienna, Santorini
}

# Create variables for each day (1 to 14)
days = [z3.Int(f'd_{i}') for i in range(1, 15)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-3)
for d in days:
    s.add(z3.And(d >= 0, d < 4))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 3)  # Amsterdam
s.add(z3.Count(1, days) == 7)  # Vienna
s.add(z3.Count(2, days) == 4)  # Santorini
s.add(z3.Count(3, days) == 3)  # Lyon

# Add event constraints
# Days 9 to 11 must be in Amsterdam (indices 8 to 10)
for i in range(8, 11):
    s.add(days[i] == 0)
# Days 7 to 9 must be in Lyon (indices 6 to 8)
for i in range(6, 9):
    s.add(days[i] == 3)

# Add transition constraints between consecutive days
for i in range(14):
    current_day = days[i]
    next_day = days[i+1] if i < 13 else None
    if i < 13:
        for a in range(4):
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