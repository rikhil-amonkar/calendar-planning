from z3 import *

# Define cities and their codes
cities = {
    'Reykjavik': 0,
    'Stockholm': 1,
    'Porto': 2,
    'Nice': 3,
    'Venice': 4,
    'Vienna': 5,
    'Split': 6,
    'Copenhagen': 7
}

# Required days for each city (excluding fixed ones)
required_days = {
    3: 3,  # Nice
    4: 4,  # Venice
    6: 3,  # Split
    7: 2,  # Copenhagen
}

# Direct flights (bidirectional)
flights = [
    (7, 5), (3, 1), (6, 7), (3, 0), (3, 2), (0, 5), (1, 7), (3, 4), (3, 5),
    (0, 7), (3, 7), (1, 5), (4, 5), (7, 2), (0, 1), (1, 6), (6, 5), (7, 4), (5, 2)
]
flight_pairs = []
for a, b in flights:
    flight_pairs.append((a, b))
    flight_pairs.append((b, a))

s = Solver()

# Pre-Reykjavik segment (days 1-3)
pre_city = Int('pre_city')
pre_start = 1
pre_end = 3
s.add(Or(pre_city == 3, pre_city == 4, pre_city == 6, pre_city == 7))  # Nice, Venice, Split, Copenhagen
s.add(Or([And(pre_city == a, 0 == b) for a, b in flight_pairs if b == 0]))  # Flight to Reykjavik

# Mid segment (days 5-11) between Stockholm and Vienna
mid_city = Int('mid_city')
mid_start = 5
mid_end = 11
s.add(Or(mid_city == 3, mid_city == 4, mid_city == 6, mid_city == 7))  # Nice, Venice, Split, Copenhagen
s.add(Or([And(1 == a, mid_city == b) for a, b in flight_pairs]))  # Flight from Stockholm
s.add(Or([And(mid_city == a, 5 == b) for a, b in flight_pairs]))  # Flight to Vienna

# Ensure required days are met
s.add(pre_end - pre_start + 1 >= required_days[pre_city])
s.add(mid_end - mid_start + 1 >= required_days[mid_city])

# Ensure all cities are covered
s.add(Distinct([pre_city, mid_city]))
city_coverage = [Or(pre_city == c, mid_city == c) for c in [3, 4, 6, 7]]
s.add(And(city_coverage))

if s.check() == sat:
    m = s.model()
    pre = m.evaluate(pre_city).as_long()
    mid = m.evaluate(mid_city).as_long()
    pre_name = [k for k, v in cities.items() if v == pre][0]
    mid_name = [k for k, v in cities.items() if v == mid][0]
    
    print("Day Plan:")
    print(f"Stay in {pre_name} from day 1 to day 3")
    print(f"Stay in Reykjavik from day 3 to day 4")
    print(f"Stay in Stockholm from day 4 to day 5")
    print(f"Stay in {mid_name} from day 5 to day 11")
    print(f"Stay in Vienna from day 11 to day 13")
    print(f"Stay in Porto from day 13 to day 17")
else:
    print("No valid plan found.")