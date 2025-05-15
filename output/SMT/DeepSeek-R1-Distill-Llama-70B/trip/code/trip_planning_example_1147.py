import z3

# Define cities and their IDs
cities = ['Brussels', 'Helsinki', 'Split', 'Dubrovnik', 'Istanbul', 'Milan', 'Vilnius', 'Frankfurt']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1, 2, 3, 4, 5, 6, 7],  # Brussels can fly to Helsinki, Split, Dubrovnik, Istanbul, Milan, Vilnius, Frankfurt
    1: [0, 2, 3, 4, 5, 6, 7],  # Helsinki can fly to Brussels, Split, Dubrovnik, Istanbul, Milan, Vilnius, Frankfurt
    2: [0, 1, 3, 4, 5, 6, 7],  # Split can fly to Brussels, Helsinki, Dubrovnik, Istanbul, Milan, Vilnius, Frankfurt
    3: [0, 1, 2, 4, 5, 6, 7],  # Dubrovnik can fly to Brussels, Helsinki, Split, Istanbul, Milan, Vilnius, Frankfurt
    4: [0, 1, 2, 3, 5, 6, 7],  # Istanbul can fly to Brussels, Helsinki, Split, Dubrovnik, Milan, Vilnius, Frankfurt
    5: [0, 1, 2, 3, 4, 6, 7],  # Milan can fly to Brussels, Helsinki, Split, Dubrovnik, Istanbul, Vilnius, Frankfurt
    6: [0, 1, 2, 3, 4, 5, 7],  # Vilnius can fly to Brussels, Helsinki, Split, Dubrovnik, Istanbul, Milan, Frankfurt
    7: [0, 1, 2, 3, 4, 5, 6],  # Frankfurt can fly to Brussels, Helsinki, Split, Dubrovnik, Istanbul, Milan, Vilnius
}

# Create variables for each day (1 to 22)
days = [z3.Int(f'd_{i}') for i in range(1, 23)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-7)
for d in days:
    s.add(z3.And(d >= 0, d < 8))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 3)  # Brussels
s.add(z3.Count(1, days) == 3)  # Helsinki
s.add(z3.Count(2, days) == 4)  # Split
s.add(z3.Count(3, days) == 2)  # Dubrovnik
s.add(z3.Count(4, days) == 5)  # Istanbul
s.add(z3.Count(5, days) == 4)  # Milan
s.add(z3.Count(6, days) == 5)  # Vilnius
s.add(z3.Count(7, days) == 3)  # Frankfurt

# Add event constraints
# Days 1 to 5 must be in Istanbul (indices 0 to 4)
for i in range(5):
    s.add(days[i] == 4)
# Days 16 to 18 must be in Frankfurt (indices 15 to 17)
for i in range(15, 18):
    s.add(days[i] == 7)
# Days 18 to 22 must be in Vilnius (indices 17 to 21)
for i in range(17, 22):
    s.add(days[i] == 6)

# Add transition constraints between consecutive days
for i in range(22):
    current_day = days[i]
    next_day = days[i+1] if i < 21 else None
    if i < 21:
        for a in range(8):
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