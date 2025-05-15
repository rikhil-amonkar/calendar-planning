import z3

# Define cities and their IDs
cities = ['Seville', 'Vilnius', 'Santorini', 'London', 'Stuttgart', 'Dublin', 'Frankfurt']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [5],        # Seville can fly to Dublin
    1: [6],        # Vilnius can fly to Frankfurt
    2: [5],        # Santorini can fly to Dublin
    3: [5, 2],     # London can fly to Dublin and Santorini
    4: [3],        # Stuttgart can fly to London
    5: [0, 2, 6, 3],  # Dublin can fly to Seville, Santorini, Frankfurt, and London
    6: [1, 4, 5, 3]   # Frankfurt can fly to Vilnius, Stuttgart, Dublin, and London
}

# Create variables for each day (1 to 17)
days = [z3.Int(f'd_{i}') for i in range(1, 18)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-6)
for d in days:
    s.add(z3.And(d >= 0, d < 7))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 5)  # Seville
s.add(z3.Count(1, days) == 3)  # Vilnius
s.add(z3.Count(2, days) == 2)  # Santorini
s.add(z3.Count(3, days) == 2)  # London
s.add(z3.Count(4, days) == 3)  # Stuttgart
s.add(z3.Count(5, days) == 3)  # Dublin
s.add(z3.Count(6, days) == 5)  # Frankfurt

# Add event constraints
# Days 1-5 must be in Seville (indices 0-4)
for i in range(5):
    s.add(days[i] == 0)
# Days 7-9 must be in Stuttgart (indices 6-8)
for i in range(6, 9):
    s.add(days[i] == 4)
# Days 9-10 must be in London (indices 8-9)
for i in range(8, 10):
    s.add(days[i] == 3)

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