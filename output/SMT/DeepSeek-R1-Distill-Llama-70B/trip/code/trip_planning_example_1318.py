import z3

# Define cities and their IDs
cities = ['Oslo', 'Helsinki', 'Edinburgh', 'Riga', 'Tallinn', 'Budapest', 'Vilnius', 'Porto', 'Geneva']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [7, 1, 2, 3, 4, 5, 6, 8],  # Oslo can fly to Porto, Helsinki, Edinburgh, Riga, Tallinn, Budapest, Vilnius, Geneva
    1: [0, 2, 3, 4, 5, 6, 7, 8],  # Helsinki can fly to Oslo, Edinburgh, Riga, Tallinn, Budapest, Vilnius, Porto, Geneva
    2: [0, 1, 3, 4, 5, 6, 7, 8],  # Edinburgh can fly to Oslo, Helsinki, Riga, Tallinn, Budapest, Vilnius, Porto, Geneva
    3: [0, 1, 2, 4, 5, 6, 7, 8],  # Riga can fly to Oslo, Helsinki, Edinburgh, Tallinn, Budapest, Vilnius, Porto, Geneva
    4: [0, 1, 2, 3, 5, 6, 7, 8],  # Tallinn can fly to Oslo, Helsinki, Edinburgh, Riga, Budapest, Vilnius, Porto, Geneva
    5: [0, 1, 2, 3, 4, 6, 7, 8],  # Budapest can fly to Oslo, Helsinki, Edinburgh, Riga, Tallinn, Vilnius, Porto, Geneva
    6: [0, 1, 2, 3, 4, 5, 7, 8],  # Vilnius can fly to Oslo, Helsinki, Edinburgh, Riga, Tallinn, Budapest, Porto, Geneva
    7: [0, 1, 2, 3, 4, 5, 6, 8],  # Porto can fly to Oslo, Helsinki, Edinburgh, Riga, Tallinn, Budapest, Vilnius, Geneva
    8: [0, 1, 2, 3, 4, 5, 6, 7]   # Geneva can fly to Oslo, Helsinki, Edinburgh, Riga, Tallinn, Budapest, Vilnius, Porto
}

# Create variables for each day (1 to 25)
days = [z3.Int(f'd_{i}') for i in range(1, 26)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-8)
for d in days:
    s.add(z3.And(d >= 0, d < 9))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 2)  # Oslo
s.add(z3.Count(1, days) == 2)  # Helsinki
s.add(z3.Count(2, days) == 3)  # Edinburgh
s.add(z3.Count(3, days) == 2)  # Riga
s.add(z3.Count(4, days) == 5)  # Tallinn
s.add(z3.Count(5, days) == 5)  # Budapest
s.add(z3.Count(6, days) == 5)  # Vilnius
s.add(z3.Count(7, days) == 5)  # Porto
s.add(z3.Count(8, days) == 4)  # Geneva

# Add event constraints
# Days 24 and 25 must be in Oslo (indices 23 and 24)
s.add(days[23] == 0)
s.add(days[24] == 0)
# Days 4 to 8 must be in Tallinn (indices 3 to 7)
for i in range(3, 8):
    s.add(days[i] == 4)

# Add transition constraints between consecutive days
for i in range(25):
    current_day = days[i]
    next_day = days[i+1] if i < 24 else None
    if i < 24:
        for a in range(9):
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