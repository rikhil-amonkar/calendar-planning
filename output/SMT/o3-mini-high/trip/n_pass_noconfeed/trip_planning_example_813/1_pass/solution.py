from z3 import *
import json

# Mapping of city indices to names and required durations.
# 0: Seville (5 days)
# 1: Vilnius (3 days)
# 2: Santorini (2 days)
# 3: London (2 days)
# 4: Stuttgart (3 days)
# 5: Dublin (3 days)
# 6: Frankfurt (5 days)
city_names = {
    0: "Seville",
    1: "Vilnius",
    2: "Santorini",
    3: "London",
    4: "Stuttgart",
    5: "Dublin",
    6: "Frankfurt"
}
durations = {
    0: 5,
    1: 3,
    2: 2,
    3: 2,
    4: 3,
    5: 3,
    6: 5
}

# Allowed direct flight connections (bidirectional pairs)
allowed_pairs = [
    (6, 5), (5, 6),  # Frankfurt <-> Dublin
    (6, 3), (3, 6),  # Frankfurt <-> London
    (3, 5), (5, 3),  # London <-> Dublin
    (1, 6), (6, 1),  # Vilnius <-> Frankfurt
    (6, 4), (4, 6),  # Frankfurt <-> Stuttgart
    (5, 0), (0, 5),  # Dublin <-> Seville
    (3, 2), (2, 3),  # London <-> Santorini
    (4, 3), (3, 4),  # Stuttgart <-> London
    (2, 5), (5, 2)   # Santorini <-> Dublin
]

# Create solver
solver = Solver()

# Create 7 integer variables for the order (each representing a city index 0..6)
order = [Int(f"order_{i}") for i in range(7)]
for o in order:
    solver.add(o >= 0, o < 7)
solver.add(Distinct(order))

# Create 7 integer variables for the start day of each city visit segment
s = [Int(f"s_{i}") for i in range(7)]
for si in s:
    solver.add(si >= 1, si <= 17)

# Set the start day of the trip
solver.add(s[0] == 1)

# Helper: duration function as Z3 expression based on city index variable.
def duration(city):
    return If(city == 0, 5,
           If(city == 1, 3,
           If(city == 2, 2,
           If(city == 3, 2,
           If(city == 4, 3,
           If(city == 5, 3, 5))))))

# Add timeline constraints.
# For each segment i, the number of days spent in the city is duration(order[i]) 
# and if you fly on the departure day it's counted in both cities.
for i in range(6):
    # s[i+1] should be the same as the departure day from city i (i.e., last day of city i's segment).
    solver.add(s[i+1] == s[i] + duration(order[i]) - 1)
# The final segment must end on day 17 (accounting for the overlap rule).
solver.add(s[6] + duration(order[6]) - 1 == 17)

# Add flight connectivity constraints between consecutive cities in the order.
for i in range(6):
    conn = []
    for (a, b) in allowed_pairs:
        conn.append(And(order[i] == a, order[i+1] == b))
    solver.add(Or(conn))

# Add meeting constraint for London:
# If London (city index 3) is visited, then the stay (which is 2 days) must include day 9 or day 10.
for i in range(7):
    solver.add(Implies(order[i] == 3,
                Or(And(s[i] <= 9, 9 <= s[i] + 2 - 1),
                   And(s[i] <= 10, 10 <= s[i] + 2 - 1)
                  )
           ))

# Add relatives meeting constraint for Stuttgart:
# If Stuttgart (city index 4) is visited, then the stay (3 days) must include at least one day from 7, 8, or 9.
for i in range(7):
    solver.add(Implies(order[i] == 4,
                Or(And(s[i] <= 7, 7 <= s[i] + 3 - 1),
                   And(s[i] <= 8, 8 <= s[i] + 3 - 1),
                   And(s[i] <= 9, 9 <= s[i] + 3 - 1)
                  )
           ))

# Solve the constraints.
if solver.check() == sat:
    model = solver.model()
    
    itinerary = []
    # Compute the itinerary segments from the model.
    for i in range(7):
        city_val = model.evaluate(order[i]).as_long()
        start_day = model.evaluate(s[i]).as_long()
        # Compute end day using the fixed duration for that city.
        end_day = start_day + durations[city_val] - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_names[city_val]
        })
    
    # Output as JSON.
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"error": "No valid itinerary found"}))