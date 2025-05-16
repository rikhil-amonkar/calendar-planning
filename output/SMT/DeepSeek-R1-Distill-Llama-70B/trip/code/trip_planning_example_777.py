import z3

# Define cities and their IDs
cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1, 3, 5],  # Dublin can fly to Helsinki, Reykjavik, Tallinn
    1: [0, 2, 3, 4, 5],  # Helsinki can fly to Dublin, Riga, Reykjavik, Vienna, Tallinn
    2: [1, 3, 4],  # Riga can fly to Helsinki, Reykjavik, Vienna
    3: [0, 1, 2, 4],  # Reykjavik can fly to Dublin, Helsinki, Riga, Vienna
    4: [1, 2, 3],  # Vienna can fly to Helsinki, Riga, Reykjavik
    5: [0, 1]  # Tallinn can fly to Dublin, Helsinki
}

# Create variables for each day (1 to 15)
days = [z3.Int(f'd_{i}') for i in range(1, 16)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-5)
for d in days:
    s.add(z3.And(d >= 0, d < 6))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 5)  # Dublin
s.add(z3.Count(1, days) == 3)  # Helsinki
s.add(z3.Count(2, days) == 3)  # Riga
s.add(z3.Count(3, days) == 2)  # Reykjavik
s.add(z3.Count(4, days) == 2)  # Vienna
s.add(z3.Count(5, days) == 5)  # Tallinn

# Add event constraints
# Days 3 to 5 must be in Helsinki (indices 2 to 4)
for i in range(2, 5):
    s.add(days[i] == 1)
# Days 2 to 3 must be in Vienna (indices 1 to 2)
s.add(days[1] == 4)
s.add(days[2] == 4)
# Days 7 to 11 must be in Tallinn (indices 6 to 10)
for i in range(6, 11):
    s.add(days[i] == 5)

# Add transition constraints between consecutive days
for i in range(15):
    current_day = days[i]
    next_day = days[i+1] if i < 14 else None
    if i < 14:
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