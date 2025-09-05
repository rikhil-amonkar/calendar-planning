from z3 import *
import json

# Mapping for cities:
# 0: Amsterdam, 1: Edinburgh, 2: Brussels, 3: Berlin, 4: Vienna, 5: Reykjavik
city_names = {0: "Amsterdam", 1: "Edinburgh", 2: "Brussels", 3: "Berlin", 4: "Vienna", 5: "Reykjavik"}
durations = {0: 4, 1: 5, 2: 5, 3: 4, 4: 5, 5: 5}

# Create SMT variables for city order (6 positions), start days, and event days.
cities = [Int(f"city_{i}") for i in range(6)]
starts = [Int(f"start_{i}") for i in range(6)]
# Event days: For Amsterdam (visit relatives), Berlin (meet friend), Reykjavik (workshop)
event_a = Int("event_a")  # Must occur in Amsterdam between day 5 and 8.
event_b = Int("event_b")  # Must occur in Berlin between day 16 and 19.
event_r = Int("event_r")  # Must occur in Reykjavik between day 12 and 16.

# Helper function to return the duration expression based on the city chosen.
def duration_expr(city_var):
    return If(city_var == 0, 4,
           If(city_var == 1, 5,
           If(city_var == 2, 5,
           If(city_var == 3, 4,
           If(city_var == 4, 5,
           If(city_var == 5, 5, 0))))))

# Allowed flights (direct connections) -- flights are bidirectional.
def allowed_flight(a, b):
    return Or(
        # Edinburgh and Amsterdam: {1,0}
        And(a == 1, b == 0), And(a == 0, b == 1),
        # Amsterdam and Berlin: {0,3}
        And(a == 0, b == 3), And(a == 3, b == 0),
        # Edinburgh and Berlin: {1,3}
        And(a == 1, b == 3), And(a == 3, b == 1),
        # Amsterdam and Vienna: {0,4}
        And(a == 0, b == 4), And(a == 4, b == 0),
        # Vienna and Berlin: {4,3}
        And(a == 4, b == 3), And(a == 3, b == 4),
        # Brussels and Berlin: {2,3}
        And(a == 2, b == 3), And(a == 3, b == 2),
        # Edinburgh and Brussels: {1,2}
        And(a == 1, b == 2), And(a == 2, b == 1),
        # Vienna and Brussels: {4,2}
        And(a == 4, b == 2), And(a == 2, b == 4),
        # Amsterdam and Reykjavik: {0,5}
        And(a == 0, b == 5), And(a == 5, b == 0),
        # Reykjavik and Brussels: {5,2}
        And(a == 5, b == 2), And(a == 2, b == 5),
        # Vienna and Reykjavik: {4,5}
        And(a == 4, b == 5), And(a == 5, b == 4),
        # Reykjavik and Berlin: {5,3}
        And(a == 5, b == 3), And(a == 3, b == 5)
    )

s = Solver()

# Domain constraints for city variables: each must be between 0 and 5.
for c in cities:
    s.add(c >= 0, c <= 5)
# All six cities must be visited exactly once.
s.add(Distinct(cities))

# Timeline constraints.
# The trip starts on day 1 in the first city.
s.add(starts[0] == 1)
# For each city visited, the number of days spent is fixed.
# Note: if you fly on the last day of a city, that same day counts for both the departure city and arrival city.
for i in range(5):
    s.add(starts[i+1] == starts[i] + duration_expr(cities[i]) - 1)
# Total itinerary must span 23 days.
s.add(starts[5] + duration_expr(cities[5]) - 1 == 23)

# Flight connection constraints: consecutive cities in the itinerary must have a direct flight.
for i in range(5):
    s.add(allowed_flight(cities[i], cities[i+1]))

# Event constraints:
# Amsterdam: 4 days; must visit relatives on a day between 5 and 8 within the Amsterdam block.
for i in range(6):
    s.add(Implies(cities[i] == 0, And(event_a >= starts[i], event_a <= starts[i] + 4 - 1)))
s.add(event_a >= 5, event_a <= 8)

# Berlin: 4 days; must meet a friend on a day between 16 and 19 within the Berlin block.
for i in range(6):
    s.add(Implies(cities[i] == 3, And(event_b >= starts[i], event_b <= starts[i] + 4 - 1)))
s.add(event_b >= 16, event_b <= 19)

# Reykjavik: 5 days; must attend a workshop on a day between 12 and 16 within the Reykjavik block.
for i in range(6):
    s.add(Implies(cities[i] == 5, And(event_r >= starts[i], event_r <= starts[i] + 5 - 1)))
s.add(event_r >= 12, event_r <= 16)

# Ensure start days fall between 1 and 23.
for st in starts:
    s.add(st >= 1, st <= 23)

# Solve the SMT constraints.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(6):
        city_code = m.evaluate(cities[i]).as_long()
        city_name = city_names[city_code]
        start_day = m.evaluate(starts[i]).as_long()
        duration_days = durations[city_code]
        end_day = start_day + duration_days - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city_name})
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))