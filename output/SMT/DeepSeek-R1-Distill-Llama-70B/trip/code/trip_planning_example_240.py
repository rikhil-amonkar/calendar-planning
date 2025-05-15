import z3

# Define cities and their IDs
cities = ['Prague', 'Berlin', 'Tallinn', 'Stockholm']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [2, 3],  # Prague can fly to Tallinn (2) and Stockholm (3)
    1: [2],     # Berlin can fly to Tallinn (2)
    2: [0, 1, 3],  # Tallinn can fly to Prague (0), Berlin (1), and Stockholm (3)
    3: [0, 1, 2]  # Stockholm can fly to Prague (0), Berlin (1), and Tallinn (2)
}

# Create variables for each day (1 to 12)
days = [z3.Int(f'd_{i}') for i in range(1, 13)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-3)
for d in days:
    s.add(z3.And(d >= 0, d < 4))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 2)  # Prague
s.add(z3.Count(1, days) == 3)  # Berlin
s.add(z3.Count(2, days) == 5)  # Tallinn
s.add(z3.Count(3, days) == 5)  # Stockholm

# Add event constraints
# Days 6 and 8 must be in Berlin (indices 5 and 7)
s.add(days[5] == 1)
s.add(days[7] == 1)
# Days 8 to 12 must be in Tallinn (indices 7 to 11)
for i in range(7, 12):
    s.add(days[i] == 2)

# Add transition constraints between consecutive days
for i in range(12):
    current_day = days[i]
    next_day = days[i+1] if i < 11 else None
    if i < 11:
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