import z3

# Define cities and their IDs
cities = ['Frankfurt', 'Manchester', 'Naples', 'Valencia', 'Oslo', 'Vilnius']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1, 2, 3, 4, 5],  # Frankfurt can fly to Manchester, Naples, Valencia, Oslo, Vilnius
    1: [0, 2, 4],        # Manchester can fly to Frankfurt, Naples, Oslo
    2: [0, 1, 3, 4],     # Naples can fly to Frankfurt, Manchester, Valencia, Oslo
    3: [0, 2],           # Valencia can fly to Frankfurt, Naples
    4: [0, 1, 2, 5],     # Oslo can fly to Frankfurt, Manchester, Naples, Vilnius
    5: [0, 4]            # Vilnius can fly to Frankfurt, Oslo
}

# Create variables for each day (1 to 16)
days = [z3.Int(f'd_{i}') for i in range(1, 17)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-5)
for d in days:
    s.add(z3.And(d >= 0, d < 6))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 4)  # Frankfurt
s.add(z3.Count(1, days) == 4)  # Manchester
s.add(z3.Count(2, days) == 4)  # Naples
s.add(z3.Count(3, days) == 4)  # Valencia
s.add(z3.Count(4, days) == 3)  # Oslo
s.add(z3.Count(5, days) == 2)  # Vilnius

# Add event constraints
# Days 13 to 16 must be in Frankfurt (indices 12 to 15)
for i in range(12, 16):
    s.add(days[i] == 0)
# Days 12 and 13 must be in Vilnius (indices 11 and 12)
s.add(days[11] == 5)
s.add(days[12] == 5)

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