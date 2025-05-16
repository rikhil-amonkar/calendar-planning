import z3

# Define cities and their IDs
cities = ['Madrid', 'Dublin', 'Tallinn']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1],  # Madrid can fly to Dublin
    1: [0, 2],  # Dublin can fly to Madrid and Tallinn
    2: [1]  # Tallinn can fly to Dublin
}

# Create variables for each day (1 to 7)
days = [z3.Int(f'd_{i}') for i in range(1, 8)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-2)
for d in days:
    s.add(z3.And(d >= 0, d < 3))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 4)  # Madrid
s.add(z3.Count(1, days) == 3)  # Dublin
s.add(z3.Count(2, days) == 2)  # Tallinn

# Add event constraints: days 6 and 7 must be in Tallinn (indices 5 and 6)
s.add(days[5] == 2)
s.add(days[6] == 2)

# Add transition constraints between consecutive days
for i in range(7):
    current_day = days[i]
    next_day = days[i+1] if i < 6 else None
    if i < 6:
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