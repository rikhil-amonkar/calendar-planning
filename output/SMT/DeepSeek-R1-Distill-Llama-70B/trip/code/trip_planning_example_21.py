import z3

# Define cities and their IDs
cities = ['Venice', 'Mykonos', 'Vienna']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [2],    # Venice can fly to Vienna
    1: [2],    # Mykonos can fly to Vienna
    2: [0, 1]  # Vienna can fly to Venice and Mykonos
}

# Create variables for each day (1 to 10)
days = [z3.Int(f'd_{i}') for i in range(1, 11)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-2)
for d in days:
    s.add(z3.And(d >= 0, d < 3))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 6)  # Venice
s.add(z3.Count(1, days) == 2)  # Mykonos
s.add(z3.Count(2, days) == 4)  # Vienna

# Add workshop constraint: days 5 to 10 must be in Venice (days 5-10 are indices 4-9)
for i in range(4, 10):  # days 5 to 10
    s.add(days[i] == 0)

# Add transition constraints between consecutive days
for i in range(10):
    current_day = days[i]
    next_day = days[i+1] if i < 9 else None
    if i < 9:
        for a in range(3):
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