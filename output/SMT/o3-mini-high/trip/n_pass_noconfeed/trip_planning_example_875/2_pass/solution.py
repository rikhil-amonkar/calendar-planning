from z3 import *
import json

# Define cities and corresponding durations
cities = ["Stuttgart", "Edinburgh", "Athens", "Split", "Krakow", "Venice", "Mykonos"]
durations = {
    0: 3,  # Stuttgart
    1: 4,  # Edinburgh
    2: 4,  # Athens
    3: 2,  # Split
    4: 4,  # Krakow
    5: 5,  # Venice
    6: 4   # Mykonos
}

# Allowed flight connections (bidirectional)
allowed_flights = [
    (4, 3), (3, 4),     # Krakow <-> Split
    (3, 2), (2, 3),     # Split <-> Athens
    (1, 4), (4, 1),     # Edinburgh <-> Krakow
    (5, 0), (0, 5),     # Venice <-> Stuttgart
    (4, 0), (0, 4),     # Krakow <-> Stuttgart
    (1, 0), (0, 1),     # Edinburgh <-> Stuttgart
    (0, 2), (2, 0),     # Stuttgart <-> Athens
    (5, 1), (1, 5),     # Venice <-> Edinburgh
    (2, 6), (6, 2),     # Athens <-> Mykonos
    (5, 2), (2, 5),     # Venice <-> Athens
    (0, 3), (3, 0),     # Stuttgart <-> Split
    (1, 2), (2, 1)      # Edinburgh <-> Athens
]

# Helper function to represent duration as a Z3 expression depending on the city id.
def Duration(city):
    return If(city == 0, durations[0],
           If(city == 1, durations[1],
           If(city == 2, durations[2],
           If(city == 3, durations[3],
           If(city == 4, durations[4],
           If(city == 5, durations[5],
           If(city == 6, durations[6], 0)))))))

# Create solver instance
solver = Solver()

# Number of itinerary segments (one per city)
n = 7

# Create itinerary order variables: P[0]...P[6] are the city indices (0 to 6) in order.
P = [Int(f"P{i}") for i in range(n)]
# Create start day variables for each segment: f[0]...f[6]
f = [Int(f"f{i}") for i in range(n)]

# Constraints: Each P[i] is between 0 and 6 and they are all distinct (each city is visited exactly once)
for i in range(n):
    solver.add(P[i] >= 0, P[i] <= 6)
solver.add(Distinct(P))

# Domain for start days: they are between 1 and 20
for i in range(n):
    solver.add(f[i] >= 1, f[i] <= 20)

# The itinerary starts on Day 1.
solver.add(f[0] == 1)

# Recurrence: For i=0,...,n-2, the start day of the next city is the previous start day 
# plus the duration of the previous city minus 1 (flight day counts for both cities)
for i in range(n - 1):
    solver.add(f[i + 1] == f[i] + Duration(P[i]) - 1)

# Total trip length must be 20 days. Last segment ends on day f[n-1] + duration - 1 = 20.
solver.add(f[n - 1] + Duration(P[n - 1]) - 1 == 20)

# Flight connection constraints: consecutive cities must have a direct flight.
for i in range(n - 1):
    flight_options = []
    for (a, b) in allowed_flights:
        flight_options.append(And(P[i] == a, P[i + 1] == b))
    solver.add(Or(flight_options))

# Time-specific constraints based on desired events:

# Stuttgart workshop: In Stuttgart, which has duration 3, at least one day between 11 and 13.
# That is equivalent to: f + 2 >= 11 and f <= 13.
for i in range(n):
    solver.add(Implies(P[i] == 0, And(f[i] + 2 >= 11, f[i] <= 13)))

# Split friend meet-up: In Split (duration 2), need a day between 13 and 14.
# That is: f + 1 >= 13 and f <= 14.
for i in range(n):
    solver.add(Implies(P[i] == 3, And(f[i] + 1 >= 13, f[i] <= 14)))

# Krakow friend meet: In Krakow (duration 4), need a day between 8 and 11.
# That is: f + 3 >= 8 and f <= 11.
for i in range(n):
    solver.add(Implies(P[i] == 4, And(f[i] + 3 >= 8, f[i] <= 11)))

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    # For each segment, determine the city, start day and end day.
    for i in range(n):
        city_id = model.evaluate(P[i]).as_long()
        start_day = model.evaluate(f[i]).as_long()
        # Use the fixed durations defined in the dictionary.
        dur = durations[city_id]
        end_day = start_day + dur - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": cities[city_id]
        })
    output = {"itinerary": itinerary}
    print(json.dumps(output))
else:
    print(json.dumps({"error": "No valid itinerary found"}))