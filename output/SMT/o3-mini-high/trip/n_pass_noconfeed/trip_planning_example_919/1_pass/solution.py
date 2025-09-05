from z3 import *
import json

def get_duration(city):
    # Returns the duration (number of days) spent in a city
    # Mapping: Vienna:4, Milan:2, Rome:3, Riga:2, Lisbon:3, Vilnius:4, Oslo:3
    return If(city == 0, 4,
           If(city == 1, 2,
           If(city == 2, 3,
           If(city == 3, 2,
           If(city == 4, 3,
           If(city == 5, 4,
           If(city == 6, 3, 0)))))))

# Allowed flight transitions.
# We use the following city code mapping:
# 0: Vienna, 1: Milan, 2: Rome, 3: Riga, 4: Lisbon, 5: Vilnius, 6: Oslo
allowed_flights = [
    (3, 6), (6, 3),    # Riga and Oslo
    (2, 6), (6, 2),    # Rome and Oslo
    (0, 1), (1, 0),    # Vienna and Milan
    (0, 5), (5, 0),    # Vienna and Vilnius
    (0, 4), (4, 0),    # Vienna and Lisbon
    (3, 1), (1, 3),    # Riga and Milan
    (4, 6), (6, 4),    # Lisbon and Oslo
    (2, 3),           # from Rome to Riga (one-way)
    (2, 4), (4, 2),    # Rome and Lisbon
    (0, 3), (3, 0),    # Vienna and Riga
    (0, 2), (2, 0),    # Vienna and Rome
    (1, 6), (6, 1),    # Milan and Oslo
    (0, 6), (6, 0),    # Vienna and Oslo
    (5, 6), (6, 5),    # Vilnius and Oslo
    (3, 5),           # from Riga to Vilnius (one-way)
    (5, 1), (1, 5),    # Vilnius and Milan
    (3, 4), (4, 3),    # Riga and Lisbon
    (1, 4), (4, 1)     # Milan and Lisbon
]

# Mapping integer codes back to city names.
city_names = {
    0: "Vienna",
    1: "Milan",
    2: "Rome",
    3: "Riga",
    4: "Lisbon",
    5: "Vilnius",
    6: "Oslo"
}

# Number of cities in the itinerary
num_segments = 7  # We must visit 7 European cities

solver = Solver()

# Create an array for the order of cities visited.
cities = [Int(f"city_{i}") for i in range(num_segments)]
# Create an array for the starting day of each segment.
s_days = [Int(f"s_{i}") for i in range(num_segments)]

# Domain constraints for city variables: each city is represented by an integer 0..6.
for c in cities:
    solver.add(c >= 0, c <= 6)
solver.add(Distinct(cities))
# The trip must start in Vienna (city code 0).
solver.add(cities[0] == 0)

# Domain constraints for the starting days.
for s_day in s_days:
    solver.add(s_day >= 1, s_day <= 15)

# The itinerary starts on day 1.
solver.add(s_days[0] == 1)

# Set up the chain constraints.
# When flying from city A to city B on a given day, that day is counted for both segments.
# Thus, if a segment has duration d, and its start day is s, then it covers days s to s + d - 1.
# The next segment starts on the overlapping flight day: s[i+1] = s[i] + duration(A) - 1.
for i in range(num_segments - 1):
    solver.add(s_days[i+1] == s_days[i] + get_duration(cities[i]) - 1)

# The last segment must end on day 15.
solver.add(s_days[-1] + get_duration(cities[-1]) - 1 == 15)

# Enforce allowed flight transitions between consecutive segments.
# For each adjacent pair, the ordered pair (current city, next city) must be in allowed_flights.
for i in range(num_segments - 1):
    trans_options = []
    for (src, dst) in allowed_flights:
        trans_options.append(And(cities[i] == src, cities[i+1] == dst))
    solver.add(Or(trans_options))

# Special scheduling constraints:

# 1. In Vienna you must attend a conference on Day 1 and Day 4.
#    Since the trip starts in Vienna (city 0) and its duration is 4 days, days 1-4 are Vienna.
# 2. Visiting relatives in Lisbon must happen between day 11 and day 13.
#    For Lisbon (city code 4) with duration 3 days, require that its segment overlaps [11, 13]:
#    That is, if s is the starting day then s <= 13 and s+2 >= 11.
# 3. Meeting a friend in Oslo must occur between day 13 and day 15.
#    For Oslo (city code 6) with duration 3 days, require that its segment overlaps [13,15]:
#    That is, s <= 15 and s+2 >= 13 (which simplifies to s >= 11).
for i in range(num_segments):
    solver.add(If(cities[i] == 4, And(s_days[i] <= 13, s_days[i] + 3 - 1 >= 11), True))
    solver.add(If(cities[i] == 6, And(s_days[i] <= 15, s_days[i] + 3 - 1 >= 13), True))

# Compute a solution.
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(num_segments):
        city_val = model[cities[i]].as_long()
        start_day = model[s_days[i]].as_long()
        # Determine the duration based on the city.
        if city_val == 0:
            dur = 4
        elif city_val == 1:
            dur = 2
        elif city_val == 2:
            dur = 3
        elif city_val == 3:
            dur = 2
        elif city_val == 4:
            dur = 3
        elif city_val == 5:
            dur = 4
        elif city_val == 6:
            dur = 3
        end_day = start_day + dur - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_names[city_val]
        })
    output = {"itinerary": itinerary}
    print(json.dumps(output))
else:
    print(json.dumps({"itinerary": []}))