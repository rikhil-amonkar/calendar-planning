from z3 import Solver, Int, Or

# Step 1: Define the cities and their corresponding integer indices
cities = ['Vienna', 'Prague', 'Riga', 'Split', 'Stockholm']
city_to_idx = {city: i for i, city in enumerate(cities)}

# Step 2: Define the number of days (based on the constraints, at least 17 days are needed)
num_days = 20  # You can adjust this number depending on your full problem

# Step 3: Create Z3 integer variables for each day's city
start_city = [Int(f'day_{d}') for d in range(num_days)]

# Step 4: Initialize the Z3 solver
s = Solver()

# Step 5: Add the constraints

# Prague must be visited at least once during days 5-9 (0-based 4-8)
prague_days = [start_city[x] == city_to_idx['Prague'] for x in range(4, 9)]
s.add(Or(prague_days))

# Split must be visited at least once during days 11-13 (0-based 10-12)
split_days = [start_city[x] == city_to_idx['Split'] for x in range(10, 13)]
s.add(Or(split_days))

# Stockholm must be visited at least once during days 16-17 (0-based 15-16)
stockholm_days = [start_city[x] == city_to_idx['Stockholm'] for x in range(15, 17)]
s.add(Or(stockholm_days))

# Vienna has at least one day in 1-5 (0-based 0-4)
vienna_days = [start_city[x] == city_to_idx['Vienna'] for x in range(5)]
s.add(Or(vienna_days))

# Riga has at least one day in 15-16 (0-based 14-15)
riga_days = [start_city[x] == city_to_idx['Riga'] for x in range(14, 16)]
s.add(Or(riga_days))

# Optional: Print solver status and model
if s.check() == sat:
    m = s.model()
    for d in range(num_days):
        print(f"Day {d} → City: {cities[m[start_city[d]].as_long()]}")
else:
    print("No solution found.")