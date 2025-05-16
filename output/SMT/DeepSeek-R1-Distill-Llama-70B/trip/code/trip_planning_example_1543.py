import z3

# Define cities and their IDs
cities = ['Prague', 'Warsaw', 'Dublin', 'Athens', 'Vilnius', 'Porto', 'London', 'Seville', 'Lisbon', 'Dubrovnik']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [1, 3, 7, 8],     # Prague can fly to Warsaw (1), Athens (3), London (7), Lisbon (8)
    1: [0, 3, 4, 5, 6, 7, 8],  # Warsaw can fly to Prague (0), Athens (3), Vilnius (4), Porto (5), London (7), Lisbon (8)
    2: [3, 5, 8, 9],     # Dublin can fly to Athens (3), Porto (5), Lisbon (8), Dubrovnik (9)
    3: [0, 1, 2, 4, 5, 7, 8, 9],  # Athens can fly to Prague (0), Warsaw (1), Dublin (2), Vilnius (4), Porto (5), London (7), Lisbon (8), Dubrovnik (9)
    4: [1, 3, 5, 6, 7, 8],  # Vilnius can fly to Warsaw (1), Athens (3), Porto (5), London (6), Lisbon (7), Dubrovnik (8)
    5: [1, 2, 3, 4, 6, 7, 8, 9],  # Porto can fly to Warsaw (1), Dublin (2), Athens (3), Vilnius (4), London (6), Lisbon (7), Dubrovnik (8)
    6: [3, 5, 7, 8],     # London can fly to Athens (3), Porto (5), Lisbon (7), Dubrovnik (8)
    7: [0, 1, 3, 4, 5, 6, 8],  # Lisbon can fly to Prague (0), Warsaw (1), Athens (3), Vilnius (4), Porto (5), London (6), Dubrovnik (8)
    8: [0, 1, 3, 4, 5, 6, 7, 9],  # Dubrovnik can fly to Prague (0), Warsaw (1), Athens (3), Vilnius (4), Porto (5), London (6), Lisbon (7), Dublin (9)
    9: [2, 5, 8]  # Seville can fly to Dublin (2), Porto (5), Dubrovnik (8)
}

# Create variables for each day (1 to 26)
days = [z3.Int(f'd_{i}') for i in range(1, 27)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-9)
for d in days:
    s.add(z3.And(d >= 0, d < 10))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 3)  # Prague
s.add(z3.Count(1, days) == 4)  # Warsaw
s.add(z3.Count(2, days) == 3)  # Dublin
s.add(z3.Count(3, days) == 3)  # Athens
s.add(z3.Count(4, days) == 4)  # Vilnius
s.add(z3.Count(5, days) == 5)  # Porto
s.add(z3.Count(6, days) == 3)  # London
s.add(z3.Count(7, days) == 2)  # Seville
s.add(z3.Count(8, days) == 5)  # Lisbon
s.add(z3.Count(9, days) == 3)  # Dubrovnik

# Add event constraints
# Days 1-3 must be in Prague (indices 0-2)
for i in range(3):
    s.add(days[i] == 0)
# Days 20-23 must be in Warsaw (indices 19-22)
for i in range(19, 23):
    s.add(days[i] == 1)
# Days 3-5 must be in London (indices 2-4)
for i in range(2, 5):
    s.add(days[i] == 6)
# Days 5-9 must be in Lisbon (indices 4-8)
for i in range(4, 9):
    s.add(days[i] == 8)
# Days 16-20 must be in Porto (indices 15-19)
for i in range(15, 20):
    s.add(days[i] == 5)

# Add transition constraints between consecutive days
for i in range(26):
    current_day = days[i]
    next_day = days[i+1] if i < 25 else None
    if i < 25:
        for a in range(10):
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