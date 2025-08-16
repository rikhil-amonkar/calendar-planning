from z3 import *
import json

# We have six cities:
# 0: Dubrovnik (4 days)
# 1: Munich    (5 days) -- must cover days 4..8 (annual show)
# 2: Split     (3 days)
# 3: Milan     (3 days) -- must include at least one day between 11 and 13 (wedding)
# 4: Porto     (4 days)
# 5: Krakow    (2 days) -- must include day 8 or 9 (meeting with friends)

durations_list = [4, 5, 3, 3, 4, 2]
cities = ["Dubrovnik", "Munich", "Split", "Milan", "Porto", "Krakow"]

# Allowed direct-flight pairs (bidirectional)
allowed_pairs = [
    (0, 1), (1, 0),    # Dubrovnik <-> Munich
    (1, 4), (4, 1),    # Munich <-> Porto
    (2, 3), (3, 2),    # Split <-> Milan
    (3, 4), (4, 3),    # Milan <-> Porto
    (1, 5), (5, 1),    # Munich <-> Krakow
    (1, 3), (3, 1),    # Munich <-> Milan
    (5, 2), (2, 5),    # Krakow <-> Split
    (5, 3), (3, 5),    # Krakow <-> Milan
    (1, 2), (2, 1)     # Munich <-> Split
]

s = Solver()

n = 6  # number of cities to visit

# Create an array "order" that will contain a permutation of 0..5 indicating the visit order.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# We'll also compute start-day for each visited block.
# The idea is that if the traveler spends d days in a city and then takes a direct flight on the last day,
# that flight day counts for both the departing and the arriving city.
# So if the block for position 0 is [start_0, end_0] with end_0 = start_0 + duration - 1,
# then the next city’s block starts exactly on end_0.
start_days = [Int(f"start_{i}") for i in range(n)]
# The end day for position i is: end_i = start_i + Duration(city_i) - 1.
def end_day(i, order_i, start_i):
    # Use nested If expressions to select the proper duration from durations_list.
    return start_i + If(order_i == 0, durations_list[0],
                If(order_i == 1, durations_list[1],
                If(order_i == 2, durations_list[2],
                If(order_i == 3, durations_list[3],
                If(order_i == 4, durations_list[4],
                If(order_i == 5, durations_list[5], 0)))))) - 1

def duration_of(city_var):
    return If(city_var == 0, durations_list[0],
           If(city_var == 1, durations_list[1],
           If(city_var == 2, durations_list[2],
           If(city_var == 3, durations_list[3],
           If(city_var == 4, durations_list[4],
           If(city_var == 5, durations_list[5], 0))))))

# The itinerary must start on day 1.
s.add(start_days[0] == 1)
# For i >= 1: the start day for city i equals (end day of previous city); note: that day counts as flight day.
for i in range(1, n):
    s.add(start_days[i] == start_days[i-1] + duration_of(order[i-1]) - 1)

# The trip must end on day 16.
s.add(start_days[n-1] + duration_of(order[n-1]) - 1 == 16)

# Event constraints:
#  1. Munich (city 1) must cover the period of the annual show: days 4..8.
#     Since its block length is 5 days, the only possibility is that its block starts on day 4.
for i in range(n):
    s.add(Implies(order[i] == 1, start_days[i] == 4))

#  2. The wedding in Milan (city 3) must be between day 11 and day 13.
#     Milan’s block is 3 days long, so its start day must be between 9 and 13.
for i in range(n):
    s.add(Implies(order[i] == 3, And(start_days[i] >= 9, start_days[i] <= 13)))

#  3. In Krakow (city 5), which has a 2–day block, you must meet your friends
#     on day 8 or day 9 – so the block must cover at least one of these days.
#     That is equivalent to its start day being 7, 8, or 9.
for i in range(n):
    s.add(Implies(order[i] == 5, Or(start_days[i] == 7, start_days[i] == 8, start_days[i] == 9)))

# Flight connectivity constraint: For each consecutive pair in the order,
# the two cities must have a direct flight.
for i in range(n - 1):
    allowed = []
    for (a, b) in allowed_pairs:
        allowed.append(And(order[i] == a, order[i+1] == b))
    s.add(Or(allowed))

# Check for a solution.
if s.check() == sat:
    model = s.model()
    # Build the itinerary as a list.
    itinerary = []
    for i in range(n):
        city_idx = model.evaluate(order[i]).as_long()
        start_day = model.evaluate(start_days[i]).as_long()
        # Compute the end day for the block.
        d = durations_list[city_idx]
        end = start_day + d - 1
        itinerary.append({
            "city": cities[city_idx],
            "start_day": start_day,
            "end_day": end
        })
    # Prepare the final result dictionary.
    result = {"itinerary": itinerary}
    # Print the JSON result.
    print(json.dumps(result, indent=2))
else:
    print("No solution found")