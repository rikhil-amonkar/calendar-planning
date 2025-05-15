import z3

# Define cities and their IDs
cities = ['Mykonos', 'Krakow', 'Vilnius', 'Helsinki', 'Dubrovnik', 'Oslo', 'Madrid', 'Paris']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [6],  # Mykonos can fly to Madrid
    1: [0, 2, 3, 5, 6, 7],  # Krakow can fly to Mykonos, Vilnius, Helsinki, Oslo, Madrid, Paris
    2: [1, 3, 4, 5, 6, 7],  # Vilnius can fly to Krakow, Helsinki, Dubrovnik, Oslo, Madrid, Paris
    3: [1, 2, 4, 5, 6, 7],  # Helsinki can fly to Krakow, Vilnius, Dubrovnik, Oslo, Madrid, Paris
    4: [2, 3, 5, 6],  # Dubrovnik can fly to Vilnius, Helsinki, Oslo, Madrid
    5: [1, 2, 3, 4, 6, 7],  # Oslo can fly to Krakow, Vilnius, Helsinki, Dubrovnik, Madrid, Paris
    6: [0, 1, 2, 3, 4, 5, 7],  # Madrid can fly to Mykonos, Krakow, Vilnius, Helsinki, Dubrovnik, Oslo, Paris
    7: [1, 2, 3, 5, 6]  # Paris can fly to Krakow, Vilnius, Helsinki, Oslo, Madrid
}

# Create variables for each day (1 to 18)
days = [z3.Int(f'd_{i}') for i in range(1, 19)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-7)
for d in days:
    s.add(z3.And(d >= 0, d < 8))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 4)  # Mykonos
s.add(z3.Count(1, days) == 5)  # Krakow
s.add(z3.Count(2, days) == 2)  # Vilnius
s.add(z3.Count(3, days) == 2)  # Helsinki
s.add(z3.Count(4, days) == 3)  # Dubrovnik
s.add(z3.Count(5, days) == 2)  # Oslo
s.add(z3.Count(6, days) == 5)  # Madrid
s.add(z3.Count(7, days) == 2)  # Paris

# Add event constraints
# Days 15 to 18 must be in Mykonos (indices 14 to 17)
for i in range(14, 18):
    s.add(days[i] == 0)
# Days 1 and 2 must be in Oslo (indices 0 and 1)
s.add(days[0] == 5)
s.add(days[1] == 5)
# Days 2 to 4 must be in Dubrovnik (indices 1 to 3)
for i in range(1, 4):
    s.add(days[i] == 4)

# Add transition constraints between consecutive days
for i in range(18):
    current_day = days[i]
    next_day = days[i+1] if i < 17 else None
    if i < 17:
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