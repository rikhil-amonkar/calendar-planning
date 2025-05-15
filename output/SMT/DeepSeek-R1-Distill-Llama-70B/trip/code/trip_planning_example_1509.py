import z3

# Define cities and their IDs
cities = ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1, 2, 3, 5, 6, 7, 8],    # Paris can fly to Warsaw (1), Krakow (2), Tallinn (3), Copenhagen (5), Helsinki (6), Oslo (7), Lyon (8)
    1: [0, 3, 4, 5, 6, 7, 9],     # Warsaw can fly to Paris (0), Tallinn (3), Riga (4), Copenhagen (5), Helsinki (6), Oslo (7), Santorini (9)
    2: [0, 5, 6, 7, 8],           # Krakow can fly to Paris (0), Copenhagen (5), Helsinki (6), Oslo (7), Lyon (8)
    3: [0, 1, 4, 5, 6, 7, 8],     # Tallinn can fly to Paris (0), Warsaw (1), Riga (4), Copenhagen (5), Helsinki (6), Oslo (7), Lyon (8)
    4: [0, 1, 3, 5, 6, 7, 8],     # Riga can fly to Paris (0), Warsaw (1), Tallinn (3), Copenhagen (5), Helsinki (6), Oslo (7), Lyon (8)
    5: [0, 1, 2, 3, 4, 6, 7, 8], # Copenhagen can fly to Paris (0), Warsaw (1), Krakow (2), Tallinn (3), Riga (4), Helsinki (6), Oslo (7), Lyon (8)
    6: [0, 1, 2, 3, 4, 5, 7, 8], # Helsinki can fly to Paris (0), Warsaw (1), Krakow (2), Tallinn (3), Riga (4), Copenhagen (5), Oslo (7), Lyon (8)
    7: [0, 1, 2, 3, 4, 5, 6, 8], # Oslo can fly to Paris (0), Warsaw (1), Krakow (2), Tallinn (3), Riga (4), Copenhagen (5), Helsinki (6), Lyon (8)
    8: [0, 2, 5, 6, 7],           # Lyon can fly to Paris (0), Krakow (2), Copenhagen (5), Helsinki (6), Oslo (7)
    9: [7]                        # Santorini can fly to Oslo (7)
}

# Create variables for each day (1 to 25)
days = [z3.Int(f'd_{i}') for i in range(1, 26)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-9)
for d in days:
    s.add(z3.And(d >= 0, d < 10))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 5)  # Paris
s.add(z3.Count(1, days) == 2)  # Warsaw
s.add(z3.Count(2, days) == 2)  # Krakow
s.add(z3.Count(3, days) == 2)  # Tallinn
s.add(z3.Count(4, days) == 2)  # Riga
s.add(z3.Count(5, days) == 5)  # Copenhagen
s.add(z3.Count(6, days) == 5)  # Helsinki
s.add(z3.Count(7, days) == 5)  # Oslo
s.add(z3.Count(8, days) == 4)  # Lyon
s.add(z3.Count(9, days) == 2)  # Santorini

# Add event constraints
# Days 4 to 8 must be in Paris (indices 3 to 7)
for i in range(3, 8):
    s.add(days[i] == 0)
# Days 17 to 18 must be in Krakow (indices 16 to 17)
for i in range(16, 18):
    s.add(days[i] == 2)
# Days 23 to 24 must be in Riga (indices 22 to 23)
for i in range(22, 24):
    s.add(days[i] == 4)
# Days 18 to 22 must be in Helsinki (indices 17 to 21)
for i in range(17, 22):
    s.add(days[i] == 6)
# Days 12 to 13 must be in Santorini (indices 11 to 12)
for i in range(11, 13):
    s.add(days[i] == 9)

# Add transition constraints between consecutive days
for i in range(25):
    current_day = days[i]
    next_day = days[i+1] if i < 24 else None
    if i < 24:
        for a in range(10):
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