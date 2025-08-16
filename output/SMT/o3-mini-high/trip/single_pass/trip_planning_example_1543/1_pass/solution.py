from z3 import *
import json

# Cities and their planned durations.
# The order of cities in this list determines their indices.
cities = ["Prague", "Warsaw", "Dublin", "Athens", "Vilnius", "Porto", "London", "Seville", "Lisbon", "Dubrovnik"]
# Durations in each city (in days). Remember that when flying the flight day is counted in both cities.
# So the “active” days for each city (without subtracting the flight‐overlap) are as follows.
durations = [3, 4, 3, 3, 4, 5, 3, 2, 5, 3]

# Special timing requirements:
#  • In Prague, you must attend a workshop sometime between day 1 and day 3 
#    => Prague's visit must include at least one day in {1,2,3} so its start day must be ≤ 3.
#  • In Warsaw, you want to meet friends between day 20 and day 23 
#    => Warsaw's 4‐day interval [s, s+3] must intersect [20,23] → s must be in [17,23].
#  • In Porto, you have a conference between day 16 and day 20 
#    => Porto's 5‐day interval [s, s+4] must intersect [16,20] → s must be between 12 and 20.
#  • In London, you attend a wedding between day 3 and day 5 
#    => London’s 3‐day interval [s, s+2] must have an overlap with {3,4,5} → s ≤ 5.
#  • In Lisbon, you visit relatives between day 5 and day 9 
#    => Lisbon’s 5‐day interval [s, s+4] must intersect [5,9] → s ≤ 9.
special_constraints = {
    # city_index: (lower_bound_on_start, upper_bound_on_start) -- if only an upper bound is given then lower = 1.
    0: (None, 3),    # Prague must start no later than day 3.
    1: (17, 23),     # Warsaw must start between 17 and 23.
    5: (12, 20),     # Porto must start between 12 and 20.
    6: (None, 5),    # London must start no later than day 5.
    8: (None, 9)     # Lisbon must start no later than day 9.
}

# Allowed direct flight connections (undirected).
# Represented as unordered pairs (using sorted order of indices according to our cities list).
allowed_pairs = [
    (0, 1),  # Prague - Warsaw
    (0, 2),  # Prague - Dublin
    (0, 3),  # Prague - Athens
    (0, 6),  # Prague - London
    (0, 8),  # Prague - Lisbon
    (1, 3),  # Warsaw - Athens
    (1, 4),  # Warsaw - Vilnius
    (1, 5),  # Warsaw - Porto
    (1, 6),  # Warsaw - London
    (1, 8),  # Warsaw - Lisbon
    (2, 3),  # Dublin - Athens
    (2, 5),  # Dublin - Porto
    (2, 6),  # Dublin - London
    (2, 7),  # Dublin - Seville
    (2, 8),  # Dublin - Lisbon
    (2, 9),  # Dublin - Dubrovnik
    (3, 4),  # Athens - Vilnius
    (3, 6),  # Athens - London  (from London-Athens)
    (3, 8),  # Athens - Lisbon
    (3, 9),  # Athens - Dubrovnik
    (5, 7),  # Porto - Seville
    (5, 8),  # Porto - Lisbon
    (6, 8),  # London - Lisbon
    (7, 8)   # Seville - Lisbon
]

# Create a Z3 solver.
solver = Solver()

n = len(cities)

# Create an "order" array: order[i] is an Int variable representing the index of the city visited in the (i+1)-th segment.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    solver.add(order[i] >= 0, order[i] < n)
solver.add(Distinct(order))  # Each city is visited exactly once.

# Create an array of start-day variables: s[i] is the day on which the visit of the i-th city (segment) starts.
# The itinerary covers day 1 to day 26.
s = [Int(f"s_{i}") for i in range(n)]

# The first city starts on day 1.
solver.add(s[0] == 1)

# For each segment i >= 1, the start day is 1 plus the sum over previous segments of (duration - 1).
# (Because the flight day – when you leave one city and arrive at the next – counts for both.)
for i in range(1, n):
    # For each previous segment j, add its "extra" days: duration - 1.
    exprs = []
    for j in range(i):
        # For each candidate city k, if order[j] == k then add (durations[k] - 1)
        terms = [If(order[j] == k, durations[k] - 1, 0) for k in range(n)]
        exprs.append(Sum(terms))
    solver.add(s[i] == 1 + Sum(exprs))

# The end of the itinerary is the end day of the last visited city.
# For the last city at position n-1, the final day is s[n-1] + (duration - 1), and this must equal 26.
last_duration = Sum([If(order[n-1] == k, durations[k] - 1, 0) for k in range(n)])
solver.add(s[n-1] + last_duration == 26)

# Impose the special timing constraints.
for i in range(n):
    city_idx = order[i]
    # For each city with a timing constraint, use implication.
    for (c_idx, (low, high)) in special_constraints.items():
        # If the city at this segment is c_idx then apply the bound(s).
        # Lower bound constraint:
        if low is not None:
            solver.add(Or(order[i] != c_idx, s[i] >= low))
        # Upper bound constraint:
        if high is not None:
            solver.add(Or(order[i] != c_idx, s[i] <= high))

# Impose flight connectivity constraints:
# For each consecutive pair of visited cities, there must be a direct flight.
for i in range(n - 1):
    a = order[i]
    b = order[i + 1]
    # For each allowed (unordered) connection (p, q), either a == p and b == q, or a == q and b == p.
    flight_options = []
    for (p, q) in allowed_pairs:
        flight_options.append(And(a == p, b == q))
        flight_options.append(And(a == q, b == p))
    solver.add(Or(flight_options))

if solver.check() == sat:
    mod = solver.model()
    # Reconstruct the itinerary.
    # For each segment i, determine: city name, start day s[i] and end day = s[i] + (duration - 1)
    itinerary = []
    for i in range(n):
        # Get the city index for position i.
        city_val = mod.evaluate(order[i]).as_long()
        start_day = mod.evaluate(s[i]).as_long()
        # The duration is given by durations[city_val]
        dur = durations[city_val]
        end_day = start_day + dur - 1
        itinerary.append({"city": cities[city_val], "start": start_day, "end": end_day})
    
    # Output the itinerary as a JSON object.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")