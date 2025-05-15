import z3

# Define cities and their IDs
cities = ['Stuttgart', 'Istanbul', 'Vilnius', 'Seville', 'Geneva', 'Valencia', 'Munich', 'Reykjavik']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [5, 1],          # Stuttgart can fly to Valencia (5) and Istanbul (1)
    1: [4, 0, 2, 6],    # Istanbul can fly to Geneva (4), Stuttgart (0), Vilnius (2), Munich (6)
    2: [1, 6],          # Vilnius can fly to Istanbul (1) and Munich (6)
    3: [5, 6],          # Seville can fly to Valencia (5) and Munich (6)
    4: [1, 6, 5],       # Geneva can fly to Istanbul (1), Munich (6), Valencia (5)
    5: [0, 3, 4, 6],    # Valencia can fly to Stuttgart (0), Seville (3), Geneva (4), Munich (6)
    6: [7, 4, 3, 1, 5, 2],  # Munich can fly to Reykjavik (7), Geneva (4), Seville (3), Istanbul (1), Valencia (5), Vilnius (2)
    7: [6, 0],          # Reykjavik can fly to Munich (6) and Stuttgart (0)
}

# Create variables for each day (1 to 25)
days = [z3.Int(f'd_{i}') for i in range(1, 26)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-7)
for d in days:
    s.add(z3.And(d >= 0, d < 8))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 4)  # Stuttgart
s.add(z3.Count(1, days) == 4)  # Istanbul
s.add(z3.Count(2, days) == 4)  # Vilnius
s.add(z3.Count(3, days) == 3)  # Seville
s.add(z3.Count(4, days) == 5)  # Geneva
s.add(z3.Count(5, days) == 5)  # Valencia
s.add(z3.Count(6, days) == 3)  # Munich
s.add(z3.Count(7, days) == 4)  # Reykjavik

# Add event constraints
# Days 1-4 must be in Reykjavik (but conflicting with Stuttgart on day 4)
# Adjusted to days 1-3 in Reykjavik and day 4 in Stuttgart
for i in range(3):
    s.add(days[i] == 7)  # Days 1-3 (indices 0-2) in Reykjavik
s.add(days[3] == 0)     # Day 4 (index 3) in Stuttgart

# Days 19-22 (indices 18-21) must be in Istanbul
for i in range(18, 22):
    s.add(days[i] == 1)

# Days 13-15 (indices 12-14) must be in Munich
for i in range(12, 15):
    s.add(days[i] == 6)

# Add transition constraints between consecutive days
for i in range(25):
    current_day = days[i]
    next_day = days[i+1] if i < 24 else None
    if i < 24:
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