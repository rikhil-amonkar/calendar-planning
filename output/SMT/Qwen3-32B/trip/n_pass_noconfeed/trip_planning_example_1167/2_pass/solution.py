from z3 import *
import json

# Define city indices and names
city_names = ["Mykonos", "Naples", "Venice", "Istanbul", "Dublin", "Frankfurt", "Krakow", "Brussels"]

# Durations for each city
durations = {
    0: 4,  # Mykonos
    1: 4,  # Naples
    2: 3,  # Venice
    3: 3,  # Istanbul
    4: 5,  # Dublin
    5: 3,  # Frankfurt
    6: 4,  # Krakow
    7: 2,  # Brussels
}

# Create a Z3 array for durations
duration_array = K(IntSort(), 0)  # Initialize array with 0s
for idx, dur in durations.items():
    duration_array = Store(duration_array, idx, dur)

# Direct flight pairs (bidirectional)
direct_flights = [
    (0, 1), (1, 0),  # Mykonos-Naples
    (2, 3), (3, 2),  # Venice-Istanbul
    (5, 6), (6, 5),  # Frankfurt-Krakow
    (1, 4), (4, 1),  # Naples-Dublin
    (6, 7), (7, 6),  # Krakow-Brussels
    (1, 3), (3, 1),  # Naples-Istanbul
    (1, 7), (7, 1),  # Naples-Brussels
    (3, 5), (5, 3),  # Istanbul-Frankfurt
    (3, 6), (6, 3),  # Istanbul-Krakow
    (3, 7), (7, 3),  # Istanbul-Brussels
    (2, 5), (5, 2),  # Venice-Frankfurt
    (1, 5), (5, 1),  # Naples-Frankfurt
    (4, 6), (6, 4),  # Dublin-Krakow
    (2, 7), (7, 2),  # Venice-Brussels
    (1, 2), (2, 1),  # Naples-Venice
    (3, 4), (4, 3),  # Istanbul-Dublin
    (2, 4), (4, 2),  # Venice-Dublin
    (4, 5), (5, 4),  # Dublin-Frankfurt
]

# Create Z3 solver
s = Solver()

# Define city sequence variables
cities = [Int(f'city_{i}') for i in range(8)]

# Add constraints for fixed positions
s.add(Distinct(cities))
s.add(cities[0] == 0)  # Mykonos
s.add(cities[3] == 3)  # Istanbul
s.add(cities[4] == 4)  # Dublin
s.add(cities[5] == 5)  # Frankfurt

# Define start and end day variables
start_days = [Int(f'start_{i}') for i in range(8)]
end_days = [Int(f'end_{i}') for i in range(8)]

# Add constraints for start/end days
for i in range(8):
    s.add(end_days[i] == start_days[i] + Select(duration_array, cities[i]) - 1)

for i in range(1, 8):
    s.add(start_days[i] == end_days[i-1])

# Add fixed start day constraints
s.add(start_days[0] == 1)  # Mykonos starts on day 1
s.add(start_days[3] == 9)   # Istanbul starts on day 9
s.add(start_days[4] == 11)  # Dublin starts on day 11
s.add(start_days[5] == 15)  # Frankfurt starts on day 15

# Add direct flight constraints between consecutive cities
for i in range(7):
    current = cities[i]
    next_city = cities[i+1]
    allowed = []
    for a, b in direct_flights:
        allowed.append(And(current == a, next_city == b))
    s.add(Or(allowed))

# Check for solution
if s.check() == sat:
    model = s.model()
    
    # Extract city sequence
    cities_sequence = [model.evaluate(c).as_long() for c in cities]
    
    # Extract start and end days
    start_days_values = [model.evaluate(sd).as_long() for sd in start_days]
    end_days_values = [model.evaluate(ed).as_long() for ed in end_days]
    
    # Generate itinerary
    itinerary = []
    for i in range(8):
        city_idx = cities_sequence[i]
        city_name = city_names[city_idx]
        start = start_days_values[i]
        end = end_days_values[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city_name})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")