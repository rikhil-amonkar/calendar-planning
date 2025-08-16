from z3 import *

# Duration for each city based on the index:
# 0: Venice=4, 1: Barcelona=3, 2: Copenhagen=4, 3: Lyon=4, 4: Reykjavik=4,
# 5: Dubrovnik=5, 6: Athens=2, 7: Tallinn=5, 8: Munich=3.
def get_duration(city):
    return If(city == 0, 4,
           If(city == 1, 3,
           If(city == 2, 4,
           If(city == 3, 4,
           If(city == 4, 4,
           If(city == 5, 5,
           If(city == 6, 2,
           If(city == 7, 5,
           If(city == 8, 3, 0)))))))))

# Map city indices to names.
city_names = {
    0: "Venice",
    1: "Barcelona",
    2: "Copenhagen",
    3: "Lyon",
    4: "Reykjavik",
    5: "Dubrovnik",
    6: "Athens",
    7: "Tallinn",
    8: "Munich"
}

# Allowed direct-flight connections (most are given as "City A and City B").
# (For our model we assume the flights are bidirectional.)
base_allowed = [
    (2, 6),   # Copenhagen and Athens
    (2, 5),   # Copenhagen and Dubrovnik
    (8, 7),   # Munich and Tallinn
    (2, 8),   # Copenhagen and Munich
    (0, 8),   # Venice and Munich
    (4, 6),   # Reykjavik to Athens (we assume symmetry)
    (6, 5),   # Athens and Dubrovnik
    (0, 6),   # Venice and Athens
    (3, 1),   # Lyon and Barcelona
    (2, 4),   # Copenhagen and Reykjavik
    (4, 8),   # Reykjavik and Munich
    (6, 8),   # Athens and Munich
    (3, 8),   # Lyon and Munich
    (1, 4),   # Barcelona and Reykjavik
    (0, 2),   # Venice and Copenhagen
    (1, 5),   # Barcelona and Dubrovnik
    (3, 0),   # Lyon and Venice
    (5, 8),   # Dubrovnik and Munich
    (1, 6),   # Barcelona and Athens
    (2, 1),   # Copenhagen and Barcelona
    (0, 1),   # Venice and Barcelona
    (1, 8),   # Barcelona and Munich
    (1, 7),   # Barcelona and Tallinn
    (2, 7)    # Copenhagen and Tallinn
]
# Make sure flights are symmetric.
allowed_flights = set()
for (a, b) in base_allowed:
    allowed_flights.add((a, b))
    allowed_flights.add((b, a))
allowed_flights = list(allowed_flights)

# Create the Z3 solver.
s = Solver()

# Create 9 integer variables representing the order (permutation) in which the 9 cities are visited.
order_vars = [Int("order_%d" % i) for i in range(9)]
for var in order_vars:
    s.add(var >= 0, var <= 8)
s.add(Distinct(order_vars))  # Ensure each city appears exactly once.

# Create start times for each segment (i.e. the day the visit to that city begins).
start_vars = [Int("start_%d" % i) for i in range(9)]
# Trip starts on day 1.
s.add(start_vars[0] == 1)
# For each subsequent segment, the start day equals the previous segment’s start plus that city’s duration minus one
# (because the flight day counts for both cities).
for i in range(1, 9):
    s.add(start_vars[i] == start_vars[i-1] + get_duration(order_vars[i-1]) - 1)
# The last segment must end on day 26:
s.add(start_vars[8] + get_duration(order_vars[8]) - 1 == 26)

# For each leg of the trip, the two consecutive cities must have a direct flight.
for i in range(8):
    a = order_vars[i]
    b = order_vars[i+1]
    flight_options = [And(a == x, b == y) for (x, y) in allowed_flights]
    s.add(Or(flight_options))

# Impose the time–window constraints (using the fact that a city’s segment runs from start to start+duration-1):
#  • Barcelona (index 1) must be visited so that its days intersect [10, 12]:
for i in range(9):
    s.add(Implies(order_vars[i] == 1, And(start_vars[i] >= 8, start_vars[i] <= 12)))
#  • Copenhagen (index 2) must intersect [7, 10]:
for i in range(9):
    s.add(Implies(order_vars[i] == 2, And(start_vars[i] >= 4, start_vars[i] <= 10)))
#  • Dubrovnik (index 5) must intersect [16, 20]:
for i in range(9):
    s.add(Implies(order_vars[i] == 5, And(start_vars[i] >= 12, start_vars[i] <= 20)))

# Solve the model.
if s.check() == sat:
    m = s.model()
    # Reconstruct the order and start times.
    order_solution = [m.evaluate(order_vars[i]).as_long() for i in range(9)]
    start_solution = [m.evaluate(start_vars[i]).as_long() for i in range(9)]

    # Build the segments (each with a city, its start day, and end day).
    itinerary_segments = []
    for i in range(9):
        city_idx = order_solution[i]
        # Get the corresponding duration.
        if city_idx == 0: dur = 4
        elif city_idx == 1: dur = 3
        elif city_idx == 2: dur = 4
        elif city_idx == 3: dur = 4
        elif city_idx == 4: dur = 4
        elif city_idx == 5: dur = 5
        elif city_idx == 6: dur = 2
        elif city_idx == 7: dur = 5
        elif city_idx == 8: dur = 3
        seg = {
            "city": city_names[city_idx],
            "start": start_solution[i],
            "end": start_solution[i] + dur - 1
        }
        itinerary_segments.append(seg)

    # Now create a day-by-day itinerary mapping.
    # Remember: if a flight happens on day X (i.e. X = start of a segment i>0),
    # then day X counts for both the previous city (ending on day X) and the new city.
    daily = {}
    for day in range(1, 27):
        daily[day] = []
        for seg in itinerary_segments:
            if seg["start"] <= day <= seg["end"]:
                daily[day].append(seg["city"])
    # Build the final output as a list of day-to-cities mappings.
    itinerary_list = []
    for day in range(1, 27):
        itinerary_list.append({"day": day, "cities": daily[day]})
    
    import json
    output = {"itinerary": itinerary_list}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")