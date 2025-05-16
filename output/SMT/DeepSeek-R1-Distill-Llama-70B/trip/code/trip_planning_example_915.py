import z3

# Define cities and their IDs
cities = ['Bucharest', 'Venice', 'Prague', 'Frankfurt', 'Zurich', 'Florence', 'Tallinn']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [3, 5, 6],     # Bucharest can fly to Frankfurt (3), Zurich (5), Tallinn (6)
    1: [3, 4, 5],     # Venice can fly to Frankfurt (3), Zurich (4), Florence (5)
    2: [6, 5, 3, 0],  # Prague can fly to Tallinn (6), Zurich (5), Frankfurt (3), Bucharest (0)
    3: [0, 1, 2, 4, 5, 6],  # Frankfurt can fly to Bucharest (0), Venice (1), Prague (2), Zurich (4), Florence (5), Tallinn (6)
    4: [1, 2, 3, 5, 6],     # Zurich can fly to Venice (1), Prague (2), Frankfurt (3), Florence (5), Tallinn (6)
    5: [2, 3, 4, 6],        # Florence can fly to Prague (2), Frankfurt (3), Zurich (4), Tallinn (6)
    6: [2, 3, 4, 5]         # Tallinn can fly to Prague (2), Frankfurt (3), Zurich (4), Florence (5)
}

# Create variables for each day (1 to 26)
days = [z3.Int(f'd_{i}') for i in range(1, 27)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-6)
for d in days:
    s.add(z3.And(d >= 0, d < 7))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 3)  # Bucharest
s.add(z3.Count(1, days) == 5)  # Venice
s.add(z3.Count(2, days) == 4)  # Prague
s.add(z3.Count(3, days) == 5)  # Frankfurt
s.add(z3.Count(4, days) == 5)  # Zurich
s.add(z3.Count(5, days) == 5)  # Florence
s.add(z3.Count(6, days) == 5)  # Tallinn

# Add event constraints
# Days 1 to 7 must be in Prague (indices 0 to 6)
for i in range(7):
    s.add(days[i] == 2)
# Days 8 to 12 must be in Tallinn (indices 7 to 11)
for i in range(7, 12):
    s.add(days[i] == 6)
# Days 12 to 16 must be in Frankfurt (indices 11 to 15)
for i in range(11, 16):
    s.add(days[i] == 3)
# Days 22 to 26 must be in Venice (indices 21 to 25)
for i in range(21, 26):
    s.add(days[i] == 1)

# Add transition constraints between consecutive days
for i in range(26):
    current_day = days[i]
    next_day = days[i+1] if i < 25 else None
    if i < 25:
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