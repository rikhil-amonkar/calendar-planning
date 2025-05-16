import z3

# Define cities and their IDs
cities = ['Vienna', 'Milan', 'Rome', 'Riga', 'Lisbon', 'Vilnius', 'Oslo']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1, 2, 3, 4, 5, 6],  # Vienna can fly to Milan (1), Rome (2), Riga (3), Lisbon (4), Vilnius (5), Oslo (6)
    1: [0, 3, 5, 6, 4],      # Milan can fly to Vienna (0), Riga (3), Vilnius (5), Oslo (6), Lisbon (4)
    2: [0, 3, 4, 6],         # Rome can fly to Vienna (0), Riga (3), Lisbon (4), Oslo (6)
    3: [0, 1, 2, 5, 4, 6],   # Riga can fly to Vienna (0), Milan (1), Rome (2), Vilnius (5), Lisbon (4), Oslo (6)
    4: [0, 2, 3, 5, 6],      # Lisbon can fly to Vienna (0), Rome (2), Riga (3), Vilnius (5), Oslo (6)
    5: [0, 3, 1, 6],         # Vilnius can fly to Vienna (0), Riga (3), Milan (1), Oslo (6)
    6: [0, 2, 3, 4, 1]       # Oslo can fly to Vienna (0), Rome (2), Riga (3), Lisbon (4), Milan (1)
}

# Create variables for each day (1 to 15)
days = [z3.Int(f'd_{i}') for i in range(1, 16)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-6)
for d in days:
    s.add(z3.And(d >= 0, d < 7))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 4)  # Vienna
s.add(z3.Count(1, days) == 2)  # Milan
s.add(z3.Count(2, days) == 3)  # Rome
s.add(z3.Count(3, days) == 2)  # Riga
s.add(z3.Count(4, days) == 3)  # Lisbon
s.add(z3.Count(5, days) == 4)  # Vilnius
s.add(z3.Count(6, days) == 3)  # Oslo

# Add event constraints
# Days 1 and 4 must be in Vienna (indices 0 and 3)
s.add(days[0] == 0)
s.add(days[3] == 0)
# Days 11-13 must be in Lisbon (indices 10-12)
for i in range(10, 13):
    s.add(days[i] == 4)
# Days 13-15 must be in Oslo (indices 12-14)
for i in range(12, 15):
    s.add(days[i] == 6)

# Add transition constraints between consecutive days
for i in range(15):
    current_day = days[i]
    next_day = days[i+1] if i < 14 else None
    if i < 14:
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