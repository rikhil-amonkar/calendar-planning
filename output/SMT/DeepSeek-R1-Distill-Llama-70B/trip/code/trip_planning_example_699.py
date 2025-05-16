import z3

# Define cities and their IDs
cities = ['Mykonos', 'Reykjavik', 'Dublin', 'London', 'Helsinki', 'Hamburg']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [3],  # Mykonos can fly to London
    1: [2, 3, 4],  # Reykjavik can fly to Dublin, London, Helsinki
    2: [1, 3, 4, 5],  # Dublin can fly to Reykjavik, London, Helsinki, Hamburg
    3: [0, 1, 2, 4, 5],  # London can fly to Mykonos, Reykjavik, Dublin, Helsinki, Hamburg
    4: [1, 2, 3, 5],  # Helsinki can fly to Reykjavik, Dublin, London, Hamburg
    5: [2, 3, 4]  # Hamburg can fly to Dublin, London, Helsinki
}

# Create variables for each day (1 to 16)
days = [z3.Int(f'd_{i}') for i in range(1, 17)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-5)
for d in days:
    s.add(z3.And(d >= 0, d < 6))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 3)  # Mykonos
s.add(z3.Count(1, days) == 2)  # Reykjavik
s.add(z3.Count(2, days) == 5)  # Dublin
s.add(z3.Count(3, days) == 5)  # London
s.add(z3.Count(4, days) == 4)  # Helsinki
s.add(z3.Count(5, days) == 2)  # Hamburg

# Add event constraints
# Days 1 and 2 must be in Hamburg (indices 0 and 1)
s.add(days[0] == 5)
s.add(days[1] == 5)
# Days 2 to 6 must be in Dublin (indices 1 to 5)
for i in range(1, 6):
    s.add(days[i] == 2)
# Days 9 and 10 must be in Reykjavik (indices 8 and 9)
s.add(days[8] == 1)
s.add(days[9] == 1)

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