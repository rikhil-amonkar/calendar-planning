import z3

# Define cities and their IDs
cities = ['Paris', 'Florence', 'Vienna', 'Porto', 'Munich', 'Nice', 'Warsaw']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1, 3, 4, 5, 6],  # Paris can fly to Florence, Vienna, Porto, Munich, Nice
    1: [0, 2, 4, 5],      # Florence can fly to Paris, Vienna, Munich, Nice
    2: [0, 1, 3, 4, 5, 6],  # Vienna can fly to Paris, Florence, Porto, Munich, Nice, Warsaw
    3: [0, 2, 4, 5, 6],    # Porto can fly to Paris, Vienna, Munich, Nice, Warsaw
    4: [0, 1, 2, 3, 5, 6],  # Munich can fly to Paris, Florence, Vienna, Porto, Nice, Warsaw
    5: [0, 1, 2, 3, 4, 6],  # Nice can fly to Paris, Florence, Vienna, Porto, Munich, Warsaw
    6: [2, 3, 4, 5]        # Warsaw can fly to Vienna, Porto, Munich, Nice
}

# Create variables for each day (1 to 20)
days = [z3.Int(f'd_{i}') for i in range(1, 21)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-6)
for d in days:
    s.add(z3.And(d >= 0, d < 7))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 5)  # Paris
s.add(z3.Count(1, days) == 3)  # Florence
s.add(z3.Count(2, days) == 2)  # Vienna
s.add(z3.Count(3, days) == 3)  # Porto
s.add(z3.Count(4, days) == 5)  # Munich
s.add(z3.Count(5, days) == 5)  # Nice
s.add(z3.Count(6, days) == 3)  # Warsaw

# Add event constraints
# Days 1-3 must be in Porto (indices 0-2)
for i in range(3):
    s.add(days[i] == 3)
# Days 13-15 must be in Warsaw (indices 12-14)
for i in range(12, 15):
    s.add(days[i] == 6)
# Days 19-20 must be in Vienna (indices 18-19)
for i in range(18, 20):
    s.add(days[i] == 2)

# Add transition constraints between consecutive days
for i in range(20):
    current_day = days[i]
    next_day = days[i+1] if i < 19 else None
    if i < 19:
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