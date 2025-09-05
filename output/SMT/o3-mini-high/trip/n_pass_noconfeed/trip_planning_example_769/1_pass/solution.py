from z3 import *
import json

# Define city IDs
# 0: Porto, 1: Prague, 2: Reykjavik, 3: Santorini, 4: Amsterdam, 5: Munich
city_names = {0: "Porto", 1: "Prague", 2: "Reykjavik", 3: "Santorini", 4: "Amsterdam", 5: "Munich"}

# Fixed durations for each city (as given)
# Porto:5, Prague:4, Reykjavik:4, Santorini:2, Amsterdam:2, Munich:4
def city_duration(city):
    return If(city == 0, 5,
           If(city == 1, 4,
           If(city == 2, 4,
           If(city == 3, 2,
           If(city == 4, 2,
           If(city == 5, 4, 0))))))

# Allowed direct flights between cities (bidirectional)
def flight_possible(a, b):
    return Or(
        # Porto <-> Amsterdam
        And(a == 0, b == 4), And(a == 4, b == 0),
        # Munich <-> Amsterdam
        And(a == 5, b == 4), And(a == 4, b == 5),
        # Reykjavik <-> Amsterdam
        And(a == 2, b == 4), And(a == 4, b == 2),
        # Munich <-> Porto
        And(a == 5, b == 0), And(a == 0, b == 5),
        # Prague <-> Reykjavik
        And(a == 1, b == 2), And(a == 2, b == 1),
        # Reykjavik <-> Munich
        And(a == 2, b == 5), And(a == 5, b == 2),
        # Amsterdam <-> Santorini
        And(a == 4, b == 3), And(a == 3, b == 4),
        # Prague <-> Amsterdam
        And(a == 1, b == 4), And(a == 4, b == 1),
        # Prague <-> Munich
        And(a == 1, b == 5), And(a == 5, b == 1)
    )

# Number of cities and segments
n_cities = 6

# Create SMT solver
solver = Solver()

# Create ordering variables: order[i] is the city visited in segment i.
order = [Int(f"order_{i}") for i in range(n_cities)]
for i in range(n_cities):
    # each order is between 0 and 5
    solver.add(And(order[i] >= 0, order[i] < n_cities))
solver.add(Distinct(order))  # permutation constraint

# Create start day variables S[i] for each segment
S = [Int(f"S_{i}") for i in range(n_cities)]
# End day of segment i will be: E[i] = S[i] + duration(city at segment i) - 1.
# We'll use the function city_duration(order[i]) to express that.
# Constraint: The initial start day is day 1.
solver.add(S[0] == 1)
for i in range(n_cities - 1):
    # The next segment starts on the same day the previous segment ends.
    # End day for segment i: S[i] + city_duration(order[i]) - 1.
    solver.add(S[i+1] == S[i] + city_duration(order[i]) - 1)
# Total itinerary days: end day of last segment equals 16.
solver.add(S[n_cities - 1] + city_duration(order[n_cities - 1]) - 1 == 16)

# Add flight connectivity constraints for consecutive segments.
for i in range(n_cities - 1):
    solver.add(flight_possible(order[i], order[i+1]))

# Add event-specific constraints:
# 1. Wedding in Reykjavik between day 4 and day 7.
#    If a segment is Reykjavik (city 2), then its interval [S, S+3] must overlap [4,7].
#    Overlap condition: S <= 7 AND S + 3 >= 4.
for i in range(n_cities):
    solver.add(Implies(order[i] == 2, And(S[i] <= 7, S[i] + 4 - 1 >= 4)))
    
# 2. Conference in Amsterdam on day 14 and 15.
#    Amsterdam (city 4) has exactly 2 days, so require its start day to be 14.
for i in range(n_cities):
    solver.add(Implies(order[i] == 4, S[i] == 14))
    
# 3. Meeting friend in Munich between day 7 and day 10.
#    For Munich (city 5) with 4 days, interval [S, S+3] must overlap [7,10]:
#    That is: S <= 10 and S + 3 >= 7.
for i in range(n_cities):
    solver.add(Implies(order[i] == 5, And(S[i] <= 10, S[i] + 4 - 1 >= 7)))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    # Compute the segments using the model values.
    for i in range(n_cities):
        city_val = model.evaluate(order[i]).as_long()
        start_day = model.evaluate(S[i]).as_long()
        duration = None
        # Get duration based on city
        if city_val == 0:
            duration = 5
        elif city_val == 1:
            duration = 4
        elif city_val == 2:
            duration = 4
        elif city_val == 3:
            duration = 2
        elif city_val == 4:
            duration = 2
        elif city_val == 5:
            duration = 4
        end_day = start_day + duration - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_names[city_val]
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))