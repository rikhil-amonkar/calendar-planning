from z3 import *
import json

# Define the 10 cities and their required durations.
cities = [
    "Berlin",   # 0
    "Lyon",     # 1
    "Paris",    # 2
    "Riga",     # 3
    "Stockholm",# 4
    "Zurich",   # 5
    "Nice",     # 6
    "Seville",  # 7
    "Milan",    # 8
    "Naples"    # 9
]

# The required days in each city.
# (Note: When flying from one city to the next, the flight day counts in both cities.)
durations = [2, 3, 5, 2, 3, 5, 2, 3, 3, 4]

# The available direct flight connections.
# We interpret the flight connections as an undirected graph.
# For each pair (a,b) we have a direct flight if (min(a,b), max(a,b)) is in allowed_edges.
allowed_edges = [
    (0, 2),  # Berlin-Paris
    (0, 3),  # Berlin-Riga
    (0, 4),  # Berlin-Stockholm
    (0, 6),  # Berlin-Nice
    (0, 8),  # Berlin-Milan
    (0, 9),  # Berlin-Naples
    (1, 2),  # Lyon-Paris  (from "Paris and Lyon")
    (1, 6),  # Lyon-Nice   (from "Lyon and Nice")
    (2, 3),  # Paris-Riga  (from "Paris and Riga")
    (2, 4),  # Paris-Stockholm (from "Paris and Stockholm")
    (2, 5),  # Paris-Zurich (from "Paris and Zurich")
    (2, 6),  # Paris-Nice  (from "Paris and Nice")
    (2, 7),  # Paris-Seville (from "Seville and Paris")
    (2, 8),  # Paris-Milan (from "Milan and Paris")
    (2, 9),  # Paris-Naples (from "Paris and Naples")
    (3, 4),  # Riga-Stockholm (from "Stockholm and Riga")
    (3, 5),  # Riga-Zurich (from "Zurich and Riga")
    (3, 6),  # Riga-Nice  (from "Nice and Riga")
    (3, 8),  # Riga-Milan (from "Milan and Riga")
    (4, 5),  # Stockholm-Zurich (from "Zurich and Stockholm")
    (4, 6),  # Stockholm-Nice (from "Nice and Stockholm")
    (4, 8),  # Stockholm-Milan (from "Milan and Stockholm")
    (5, 6),  # Zurich-Nice (from "Nice and Zurich")
    (5, 9),  # Zurich-Naples (from "Naples and Zurich")
    (6, 9),  # Nice-Naples (from "Nice and Naples")
    (7, 8),  # Seville-Milan (from "Milan and Seville")
    (8, 9),  # Milan-Naples (from "Milan and Naples")
]

# Create the Z3 solver.
s = Solver()

n_cities = len(cities)  # 10

# We'll represent our itinerary as a permutation of the city indices.
# order[i] is the city in the i-th segment of our trip.
order = [Int(f"order_{i}") for i in range(n_cities)]
for o in order:
    s.add(o >= 0, o < n_cities)
s.add(Distinct(order))
# The wedding in Berlin is between day 1 and day 2.
# Since Berlin requires 2 days and must cover day 1, we force Berlin to be first.
s.add(order[0] == 0)

# We'll assign a start day to each city segment.
# start[i] is the day on which we begin the i-th city’s stay.
start = [Int(f"start_{i}") for i in range(n_cities)]
s.add(start[0] == 1)  # The itinerary starts on day 1.

# Define a helper function to get the duration given a Z3 city variable.
def duration(city):
    return If(city == 0, durations[0],
           If(city == 1, durations[1],
           If(city == 2, durations[2],
           If(city == 3, durations[3],
           If(city == 4, durations[4],
           If(city == 5, durations[5],
           If(city == 6, durations[6],
           If(city == 7, durations[7],
           If(city == 8, durations[8],
           If(city == 9, durations[9],
           0)))))))) 

# When flying, the flight day is counted in both the current city and the next city.
# Thus, if a city is visited from day A to day B (B = A + duration - 1),
# then the next city's start day must equal B (sharing the flight day).
for i in range(n_cities - 1):
    s.add(start[i+1] == start[i] + duration(order[i]) - 1)

# The last city must finish on day 23.
s.add(start[n_cities - 1] + duration(order[n_cities - 1]) - 1 == 23)

# Add time–event constraints:
# Nice has a workshop between day 12 and day 13.
# Since Nice requires 2 days, its only possibility is to be scheduled starting on day 12.
for i in range(n_cities):
    s.add(Implies(order[i] == 6, start[i] == 12))
    
# Stockholm has an annual show from day 20 to day 22.
# With a 3-day stay, Stockholm must start on day 20.
for i in range(n_cities):
    s.add(Implies(order[i] == 4, start[i] == 20))
    
# (Berlin’s wedding constraint is already met by forcing Berlin to start day 1.)

# Add flight connectivity constraints.
# For each consecutive pair in the itinerary, the two cities must have a direct flight.
for i in range(n_cities - 1):
    # For cities a and b at positions i and i+1,
    # ensure that one of the allowed edges holds.
    a = order[i]
    b = order[i+1]
    possible_flights = []
    for (c1, c2) in allowed_edges:
        # Because flights are bidirectional, we allow either ordering.
        possible_flights.append(And(a == c1, b == c2))
        possible_flights.append(And(a == c2, b == c1))
    s.add(Or(possible_flights))

# Check if a solution exists.
if s.check() == sat:
    m = s.model()
    
    itinerary_segments = []
    # Build the itinerary segments in order.
    for i in range(n_cities):
        city_idx = m.evaluate(order[i]).as_long()
        seg_start = m.evaluate(start[i]).as_long()
        seg_end = seg_start + durations[city_idx] - 1
        itinerary_segments.append({
            "city": cities[city_idx],
            "start": seg_start,
            "end": seg_end
        })
        
    result = {"itinerary": itinerary_segments}
    print(json.dumps(result, indent=4))
else:
    print("No solution found.")