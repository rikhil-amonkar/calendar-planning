from z3 import *

city_names = ['Helsinki', 'Madrid', 'Budapest', 'Reykjavik', 'Warsaw', 'Split']
n_days = 14

s = Solver()

base_city = [Int(f'base_{i}') for i in range(n_days)]
travel = [Bool(f'travel_{i}') for i in range(n_days)]

# Start in Helsinki
s.add(base_city[0] == 0)

# Define end-of-day city for each day
end_city = [If(travel[i], base_city[i] + 1, base_city[i]) for i in range(n_days)]

# Next day's start is previous day's end
for i in range(n_days - 1):
    s.add(base_city[i+1] == end_city[i])

# End trip in Split
s.add(end_city[n_days-1] == 5)

# City bounds and no travel from Split
for i in range(n_days):
    s.add(base_city[i] >= 0)
    s.add(base_city[i] < 5)  # Can be 0-4 (Split only via travel)
    s.add(Implies(base_city[i] == 5, Not(travel[i]))  # Can't leave Split

# Count days per city (end_city)
city_counts = []
for k in range(6):
    count = Sum([If(end_city[i] == k, 1, 0) for i in range(n_days)])
    city_counts.append(count)

# Minimum stay requirements
for k in range(5):  # Intermediate cities
    s.add(city_counts[k] >= 3)
s.add(city_counts[5] >= 1)  # Split

# Solve and output
if s.check() == sat:
    m = s.model()
    base_vals = [m.evaluate(base_city[i]).as_long() for i in range(n_days)]
    travel_vals = [m.evaluate(travel[i]) for i in range(n_days)]
    
    itinerary = []
    for i in range(n_days):
        if travel_vals[i]:
            from_city = city_names[base_vals[i]]
            to_city = city_names[base_vals[i] + 1]
            itinerary.append([from_city, to_city])
        else:
            itinerary.append([city_names[base_vals[i]]])
    print(itinerary)
else:
    print("No solution found")