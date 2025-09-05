from z3 import *
import json

# Define the list of cities and their required durations.
cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
# Durations: Dublin=5, Helsinki=3, Riga=3, Reykjavik=2, Vienna=2, Tallinn=5
def get_duration(city):
    return If(city == 0, 5,
           If(city == 1, 3,
           If(city == 2, 3,
           If(city == 3, 2,
           If(city == 4, 2,
           5)))))

# Allowed direct flight pairs (bidirectional).
# Represented as unordered pairs between indices:
allowed_pairs = [(0,1), (1,2), (2,5), (1,4), (0,2), (2,4), (3,4), (0,5), (1,3), (0,3), (1,5), (0,4)]

# Number of segments in the itinerary.
num_segments = 6

# Create SMT variables:
city_vars = [Int(f"city_{i}") for i in range(num_segments)]
start_vars = [Int(f"start_{i}") for i in range(num_segments)]
end_vars = [Int(f"end_{i}") for i in range(num_segments)]

s = Solver()

# Each city variable must be between 0 and 5 and all cities must be distinct.
for cv in city_vars:
    s.add(And(cv >= 0, cv <= 5))
s.add(Distinct(city_vars))

# Set the chain of days. The trip spans days 1 to 15.
s.add(start_vars[0] == 1)
for i in range(num_segments):
    # Each segment's duration depends on the city visited.
    s.add(end_vars[i] == start_vars[i] + get_duration(city_vars[i]) - 1)
    # Ensure the segment falls within the trip window.
    s.add(start_vars[i] >= 1, end_vars[i] <= 15)
    if i < num_segments - 1:
        # The next segment starts on the same day the previous segment ends.
        s.add(start_vars[i+1] == end_vars[i])
# The final segment must end exactly on day 15.
s.add(end_vars[num_segments - 1] == 15)

# Flight connectivity: for every consecutive pair of segments, the cities must be connected.
for i in range(num_segments - 1):
    transition_possible = []
    for (a, b) in allowed_pairs:
        # Allow either direction.
        transition_possible.append(And(city_vars[i] == a, city_vars[i+1] == b))
        transition_possible.append(And(city_vars[i] == b, city_vars[i+1] == a))
    s.add(Or(*transition_possible))

# Event constraints:
# 1. Helsinki (index 1) stay must include at least one day between day 3 and day 5.
for i in range(num_segments):
    s.add(Implies(city_vars[i] == 1,
                  Or(And(start_vars[i] <= 3, 3 <= end_vars[i]),
                     And(start_vars[i] <= 4, 4 <= end_vars[i]),
                     And(start_vars[i] <= 5, 5 <= end_vars[i]))))

# 2. Vienna (index 4) stay must include at least one day from day 2 to day 3.
for i in range(num_segments):
    s.add(Implies(city_vars[i] == 4,
                  Or(And(start_vars[i] <= 2, 2 <= end_vars[i]),
                     And(start_vars[i] <= 3, 3 <= end_vars[i]))))

# 3. Tallinn (index 5) stay must include at least one day between day 7 and day 11 (wedding).
for i in range(num_segments):
    s.add(Implies(city_vars[i] == 5,
                  Or(And(start_vars[i] <= 7, 7 <= end_vars[i]),
                     And(start_vars[i] <= 8, 8 <= end_vars[i]),
                     And(start_vars[i] <= 9, 9 <= end_vars[i]),
                     And(start_vars[i] <= 10, 10 <= end_vars[i]),
                     And(start_vars[i] <= 11, 11 <= end_vars[i]))))

# Solve the constraints and output the itinerary as JSON.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(num_segments):
        city_index = m.evaluate(city_vars[i]).as_long()
        start_day = m.evaluate(start_vars[i]).as_long()
        end_day = m.evaluate(end_vars[i]).as_long()
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": cities[city_index]
        })
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))