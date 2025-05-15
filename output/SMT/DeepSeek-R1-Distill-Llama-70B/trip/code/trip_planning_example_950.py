import z3

# Define cities and their IDs
cities = ['Mykonos', 'Riga', 'Munich', 'Bucharest', 'Rome', 'Nice', 'Krakow']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [2, 5],     # Mykonos can fly to Munich (2) and Nice (5)
    1: [0, 3, 2],  # Riga can fly to Mykonos (0), Bucharest (3), and Munich (2)
    2: [0, 1, 3, 4, 5, 6],  # Munich can fly to Mykonos (0), Riga (1), Bucharest (3), Rome (4), Nice (5), Krakow (6)
    3: [1, 2, 4, 5],  # Bucharest can fly to Riga (1), Munich (2), Rome (4), Nice (5)
    4: [2, 3, 5, 1],  # Rome can fly to Munich (2), Bucharest (3), Nice (5), Riga (1)
    5: [0, 2, 3, 4],  # Nice can fly to Mykonos (0), Munich (2), Bucharest (3), Rome (4)
    6: [2]          # Krakow can fly to Munich (2)
}

# Create variables for each day (1 to 17)
days = [z3.Int(f'd_{i}') for i in range(1, 18)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-6)
for d in days:
    s.add(z3.And(d >= 0, d < 7))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 3)  # Mykonos
s.add(z3.Count(1, days) == 3)  # Riga
s.add(z3.Count(2, days) == 4)  # Munich
s.add(z3.Count(3, days) == 4)  # Bucharest
s.add(z3.Count(4, days) == 4)  # Rome
s.add(z3.Count(5, days) == 3)  # Nice
s.add(z3.Count(6, days) == 2)  # Krakow

# Add event constraints
# Days 1 and 4 must be in Rome (indices 0 and 3)
s.add(days[0] == 4)
s.add(days[3] == 4)
# Days 4-6 must be in Mykonos (indices 3-5)
for i in range(3, 6):
    s.add(days[i] == 0)
# Days 16-17 must be in Krakow (indices 15-16)
s.add(days[15] == 6)
s.add(days[16] == 6)

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