import z3

# Define cities and their IDs
cities = ['Krakow', 'Dubrovnik', 'Frankfurt']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [2],      # Krakow can fly to Frankfurt
    1: [2],      # Dubrovnik can fly to Frankfurt
    2: [0, 1]    # Frankfurt can fly to Krakow and Dubrovnik
}

# Create variables for each day (1 to 10)
days = [z3.Int(f'd_{i}') for i in range(1, 11)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-2)
for d in days:
    s.add(z3.And(d >= 0, d < 3))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 2)  # Krakow
s.add(z3.Count(1, days) == 7)  # Dubrovnik
s.add(z3.Count(2, days) == 3)  # Frankfurt

# Add event constraints
# Days 9 and 10 must be in Krakow (indices 8 and 9)
s.add(days[8] == 0)
s.add(days[9] == 0)

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