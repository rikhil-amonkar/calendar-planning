from z3 import *
import json

# Define city names and their indices
cities = ["Venice", "Reykjavik", "Munich", "Santorini", "Manchester", "Porto", "Bucharest", "Tallinn", "Valencia", "Vienna"]
city_index = {city: idx for idx, city in enumerate(cities)}

# Required days for each city
required_days = [3, 2, 3, 3, 3, 3, 5, 4, 2, 5]  # Order: Venice, Reykjavik, Munich, Santorini, Manchester, Porto, Bucharest, Tallinn, Valencia, Vienna

# Flight connections as a list of tuples
flight_pairs = [
    ("Bucharest", "Manchester"),
    ("Munich", "Venice"),
    ("Santorini", "Manchester"),
    ("Vienna", "Reykjavik"),
    ("Venice", "Santorini"),
    ("Munich", "Porto"),
    ("Valencia", "Vienna"),
    ("Manchester", "Vienna"),
    ("Porto", "Vienna"),
    ("Venice", "Manchester"),
    ("Santorini", "Vienna"),
    ("Munich", "Manchester"),
    ("Munich", "Reykjavik"),
    ("Bucharest", "Valencia"),
    ("Venice", "Vienna"),
    ("Bucharest", "Vienna"),
    ("Porto", "Manchester"),
    ("Munich", "Vienna"),
    ("Valencia", "Porto"),
    ("Munich", "Bucharest"),
    ("Tallinn", "Munich"),
    ("Santorini", "Bucharest"),
    ("Munich", "Valencia")
]

# Create adjacency matrix
adj = [[0]*10 for _ in range(10)]
for c1, c2 in flight_pairs:
    i, j = city_index[c1], city_index[c2]
    adj[i][j] = 1
    adj[j][i] = 1

# Initialize Z3 solver
s = Solver()

# Define variables: start and end days for each city, and the sequence of visits
start = [Int(f'start_{i}') for i in range(10)]
end = [Int(f'end_{i}') for i in range(10)]
seq = [Int(f'seq_{i}') for i in range(10)]  # seq[i] is the city index at the i-th segment

# Add constraints for required days
for i in range(10):
    s.add(end[i] - start[i] + 1 == required_days[i])

# Fixed events
s.add(start[2] == 4, end[2] == 6)   # Munich: days 4-6
s.add(start[3] == 8, end[3] == 10)   # Santorini: days 8-10
s.add(start[8] == 14, end[8] == 15)  # Valencia: days 14-15

# Each city must appear exactly once in the sequence
s.add(Distinct(seq))

# Itinerary starts at day 1 and ends at day 24
s.add(start[seq[0]] == 1)
s.add(end[seq[9]] == 24)

# Consecutive segments: end of current segment is start of next
for k in range(9):
    s.add(end[seq[k]] == start[seq[k+1]])

# Flight connectivity: consecutive cities in the sequence must have a direct flight
for k in range(9):
    i = seq[k]
    j = seq[k+1]
    s.add(adj[i][j] == 1)

# Bounds for start and end days
for i in range(10):
    s.add(start[i] >= 1)
    s.add(end[i] <= 24)

# Check for solution
if s.check() == sat:
    m = s.model()
    # Extract the sequence of cities
    seq_val = [m.evaluate(seq[i]).as_long() for i in range(10)]
    # Extract start and end days for each city
    start_val = [m.evaluate(start[i]).as_long() for i in range(10)]
    end_val = [m.evaluate(end[i]).as_long() for i in range(10)]
    
    # Build itinerary: for each day, list all cities visited on that day
    itinerary = []
    for day in range(1, 25):
        for i in range(10):
            if start_val[i] <= day <= end_val[i]:
                itinerary.append({"day": day, "place": cities[i]})
    
    # Output as JSON
    result = {'itinerary': itinerary}
    print(json.dumps(result))
else:
    print("No solution found")