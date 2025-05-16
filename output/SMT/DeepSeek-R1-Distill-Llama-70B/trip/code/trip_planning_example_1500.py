import z3

# Define cities and their IDs
cities = ['Zurich', 'Bucharest', 'Hamburg', 'Barcelona', 'Reykjavik', 'Stuttgart', 'Stockholm', 'Tallinn', 'Milan', 'London']
city_id = {city: idx for idx, city in enumerate(cities)}

# Build adjacency list based on direct flights
adj = {
    0: [3, 5, 6, 7, 8],    # Zurich can fly to Barcelona, Reykjavik, Stockholm, Tallinn, Milan
    1: [3, 8],              # Bucharest can fly to Barcelona, Milan
    2: [0, 1, 3, 4, 5, 6, 7, 8],  # Hamburg can fly to Zurich, Bucharest, Barcelona, Reykjavik, Stuttgart, Stockholm, Tallinn, Milan
    3: [0, 1, 2, 4, 5, 6, 7, 8],  # Barcelona can fly to Zurich, Bucharest, Hamburg, Reykjavik, Stuttgart, Stockholm, Tallinn, Milan
    4: [0, 2, 3, 5, 6, 7, 8],     # Reykjavik can fly to Zurich, Hamburg, Barcelona, Stuttgart, Stockholm, Tallinn, Milan
    5: [2, 3, 4, 6, 7, 8],        # Stuttgart can fly to Hamburg, Barcelona, Reykjavik, Stockholm, Tallinn, Milan
    6: [0, 2, 3, 4, 5, 7, 8],     # Stockholm can fly to Zurich, Hamburg, Barcelona, Reykjavik, Stuttgart, Tallinn, Milan
    7: [2, 3, 4, 5, 6, 8],        # Tallinn can fly to Hamburg, Barcelona, Reykjavik, Stuttgart, Stockholm, Milan
    8: [0, 1, 2, 3, 4, 5, 6, 7], # Milan can fly to Zurich, Bucharest, Hamburg, Barcelona, Reykjavik, Stuttgart, Stockholm, Tallinn
    9: [2, 3, 4, 5, 6, 7, 8]      # London can fly to Hamburg, Barcelona, Reykjavik, Stuttgart, Stockholm, Tallinn, Milan
}

# Create variables for each day (1 to 28)
days = [z3.Int(f'd_{i}') for i in range(1, 29)]

# Create solver
s = z3.Solver()

# Add domain constraints: each day must be a valid city ID (0-9)
for d in days:
    s.add(z3.And(d >= 0, d < 10))

# Add constraints for the number of days in each city
s.add(z3.Count(0, days) == 2)  # Zurich
s.add(z3.Count(1, days) == 2)  # Bucharest
s.add(z3.Count(2, days) == 5)  # Hamburg
s.add(z3.Count(3, days) == 4)  # Barcelona
s.add(z3.Count(4, days) == 5)  # Reykjavik
s.add(z3.Count(5, days) == 5)  # Stuttgart
s.add(z3.Count(6, days) == 2)  # Stockholm
s.add(z3.Count(7, days) == 4)  # Tallinn
s.add(z3.Count(8, days) == 5)  # Milan
s.add(z3.Count(9, days) == 3)  # London

# Add event constraints
# Days 1-3 must be in London (indices 0-2)
for i in range(3):
    s.add(days[i] == 9)
# Days 3-7 must be in Milan (indices 2-6)
for i in range(2, 7):
    s.add(days[i] == 8)
# Days 7-8 must be in Zurich (indices 6-7)
for i in range(6, 8):
    s.add(days[i] == 0)
# Days 9-13 must be in Reykjavik (indices 8-12)
for i in range(8, 13):
    s.add(days[i] == 4)

# Add transition constraints between consecutive days
for i in range(28):
    current_day = days[i]
    next_day = days[i+1] if i < 27 else None
    if i < 27:
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