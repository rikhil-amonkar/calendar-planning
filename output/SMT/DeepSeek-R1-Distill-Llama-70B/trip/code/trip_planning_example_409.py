import z3

# Define cities and their IDs
cities = ['Hamburg', 'Zurich', 'Helsinki', 'Bucharest', 'Split']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1, 2, 3],  # Hamburg can fly to Zurich (1), Helsinki (2), Bucharest (3)
    1: [0, 2, 3, 4],  # Zurich can fly to Hamburg (0), Helsinki (2), Bucharest (3), Split (4)
    2: [0, 1, 4],  # Helsinki can fly to Hamburg (0), Zurich (1), Split (4)
    3: [0, 1],  # Bucharest can fly to Hamburg (0), Zurich (1)
    4: [1, 2, 0]  # Split can fly to Zurich (1), Helsinki (2), Hamburg (0)
}

# Create variables for each day (1 to 12)
days = [z3.Int(f'd_{i}') for i in range(1, 13)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-4)
for d in days:
    s.add(z3.And(d >= 0, d < 5))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 2)  # Hamburg
s.add(z3.Count(1, days) == 3)  # Zurich
s.add(z3.Count(2, days) == 2)  # Helsinki
s.add(z3.Count(3, days) == 2)  # Bucharest
s.add(z3.Count(4, days) == 7)  # Split

# Add event constraints
# Days 1-3 must be in Zurich (indices 0-2)
for i in range(3):
    s.add(days[i] == 1)
# Days 4 and 10 must be in Split (indices 3 and 9)
s.add(days[3] == 4)
s.add(days[9] == 4)

# Add transition constraints between consecutive days
for i in range(12):
    current_day = days[i]
    next_day = days[i+1] if i < 11 else None
    if i < 11:
        for a in range(5):
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