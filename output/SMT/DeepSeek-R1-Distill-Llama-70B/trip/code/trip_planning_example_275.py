import z3

# Define cities and their IDs
cities = ['Split', 'Vilnius', 'Santorini', 'Madrid']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1, 3],  # Split can fly to Vilnius and Madrid
    1: [0],     # Vilnius can fly to Split
    2: [],      # Santorini has no outgoing flights
    3: [0, 2]   # Madrid can fly to Split and Santorini
}

# Create variables for each day (1 to 14)
days = [z3.Int(f'd_{i}') for i in range(1, 15)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-3)
for d in days:
    s.add(z3.And(d >= 0, d < 4))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 5)  # Split
s.add(z3.Count(1, days) == 4)  # Vilnius
s.add(z3.Count(2, days) == 2)  # Santorini
s.add(z3.Count(3, days) == 6)  # Madrid

# Add event constraints
# Days 13 and 14 must be in Santorini (indices 12 and 13)
s.add(days[12] == 2)
s.add(days[13] == 2)

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