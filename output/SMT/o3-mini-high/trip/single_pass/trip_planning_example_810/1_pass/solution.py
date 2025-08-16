from z3 import Solver, Int, And, Or, Distinct, sat
import json

# Define the 7 cities and their required durations (in days)
# When flying, the flight day counts for both cities.
# Hence if city X is visited with duration d and the next city Y is reached by a flight on day (start_X + d - 1),
# then the overall total days = (sum of durations) - (number_of_transitions).
# Here: 3 + 2 + 2 + 5 + 5 + 5 + 4 = 26; there are 6 transitions, so 26 - 6 = 20 total days.
cities = ["Berlin", "Barcelona", "Lyon", "Nice", "Stockholm", "Athens", "Vilnius"]
# Required durations for each city:
durations = {
    "Berlin": 3,
    "Barcelona": 2,
    "Lyon": 2,
    "Nice": 5,
    "Stockholm": 5,
    "Athens": 5,
    "Vilnius": 4
}

# We will assign each city to a position in the itinerary: position 0...6.
# Their scheduled visit will be an interval [start_day, end_day] (both inclusive).
# When flying on the last day of a city’s block, that day counts also toward the next city's block.
# Thus, if a city is visited from S to E then its duration is E-S+1.
# And for consecutive segments, we have: start[next] = end[current].

# We also have extra events:
# - Berlin: must include day 1 and day 3 (conference).
# - Barcelona: must include days 3 and 4 (workshop between day 3 and day 4).
# - Lyon: must include days 4 and 5 (wedding between day 4 and day 5).

# Moreover, flights are only allowed between cities with a direct connection.
# The allowed (undirected) flight pairs (using the city indices below) are:
#   - Berlin (0) and Barcelona (1)
#   - Berlin (0) and Nice (3)
#   - Berlin (0) and Athens (5)
#   - Berlin (0) and Stockholm (4)
#   - Berlin (0) and Vilnius (6)
#   - Barcelona (1) and Lyon (2)
#   - Barcelona (1) and Nice (3)
#   - Barcelona (1) and Stockholm (4)
#   - Barcelona (1) and Athens (5)
#   - Lyon (2) and Nice (3)
#   - Nice (3) and Stockholm (4)
#   - Nice (3) and Athens (5)
#   - Stockholm (4) and Athens (5)
#   - Athens (5) and Vilnius (6)

# For convenience, assign indices as follows:
# Berlin -> 0, Barcelona -> 1, Lyon -> 2, Nice -> 3, Stockholm -> 4, Athens -> 5, Vilnius -> 6

# Create a Z3 solver.
solver = Solver()

# Create 7 integer variables for the itinerary order.
# itinerary[i] is the index (0..6) of the city visited in the i-th segment.
itinerary = [Int(f"itinerary_{i}") for i in range(7)]
for i in range(7):
    # Each itinerary variable must be in the range 0..6
    solver.add(itinerary[i] >= 0, itinerary[i] < 7)
solver.add(Distinct(itinerary))  # no city is visited twice

# Create 7 integer variables for the start day of each city’s visit segment.
start = [Int(f"start_{i}") for i in range(7)]

# Enforce the “chain” structure:
# The first city’s start day is fixed to day 1.
solver.add(start[0] == 1)

# The end day of the visit in segment i is: start[i] + (duration - 1), where duration depends on which city is scheduled.
# And because when flying the day is common to both segments
# we require: start[i+1] == (start[i] + duration(city at itinerary[i]) - 1)
for i in range(6):
    # Because the actual duration depends on the city, we use a conditional structure.
    # But later we will constrain the itinerary positions so that “itinerary” becomes fixed.
    # Here we “dispatch” on the value of itinerary[i].
    conds = []
    for city_idx, city in enumerate(cities):
        dur = durations[city]
        conds.append(And(itinerary[i] == city_idx, start[i+1] == start[i] + dur - 1))
    solver.add(Or(*conds))

# The overall trip ends on day 20.
# That is, for the last segment: end = start[6] + duration(city at itinerary[6]) - 1 must equal 20.
end_last = []
for city_idx, city in enumerate(cities):
    dur = durations[city]
    end_last.append(And(itinerary[6] == city_idx, start[6] + dur - 1 == 20))
solver.add(Or(*end_last))

# Now add the specific event constraints.
# Berlin (index 0): must cover days 1 and 3.
# We force Berlin to be the first visited city so that day 1 is Berlin.
solver.add(itinerary[0] == 0)
# With duration 3, Berlin’s interval will be: [start_0, start_0+2].
# Since start_0==1, Berlin’s interval is [1,3] which indeed covers days 1 and 3.

# Barcelona (index 1): must cover days 3 and 4 for the workshop.
# With duration 2 the only possibility to cover both day 3 and day 4 is to have interval [3,4].
# Because day3 must be in Barcelona, and note that flight days are double counted.
# Also, Barcelona must then come immediately after Berlin.
solver.add(itinerary[1] == 1)
# The start for segment 1 will be start[1]. From the chain constraint, since itinerary[0] is Berlin with duration 3,
# we have: start[1] == start[0] + 3 - 1 == 1+3-1 == 3.
# Thus Barcelona’s interval becomes [3, 3+2-1] = [3,4].

# Lyon (index 2): must cover days 4 and 5 for the wedding.
# With duration 2, the only possibility is interval [4,5].
solver.add(itinerary[2] == 2)
# From the chain: start[2] == start[1] + duration(Barcelona) - 1 == 3+2-1 == 4.
# So Lyon’s interval is [4,5].

# After Lyon, the remaining three cities to be scheduled are: Nice (index 3), Stockholm (index 4), Athens (index 5), and Vilnius (index 6)
# But note that we have 7 cities in total and we already fixed positions 0,1,2.
# We then use the direct flight constraints to force the order.
# The only direct flight available from Lyon is between Lyon (2) and Nice (3).
solver.add(itinerary[3] == 3)

# For positions 4, 5, and 6 we have the remaining cities {Stockholm (4), Athens (5), Vilnius (6)}.
# Now add the flight connectivity constraints.
# Define the allowed (undirected) flights as pairs (with the smaller index first):
allowed_flights = [
    (0, 1),   # Berlin and Barcelona
    (0, 3),   # Berlin and Nice
    (0, 4),   # Berlin and Stockholm
    (0, 5),   # Berlin and Athens
    (0, 6),   # Berlin and Vilnius
    (1, 2),   # Barcelona and Lyon
    (1, 3),   # Barcelona and Nice
    (1, 4),   # Barcelona and Stockholm
    (1, 5),   # Barcelona and Athens
    (2, 3),   # Lyon and Nice
    (3, 4),   # Nice and Stockholm
    (3, 5),   # Nice and Athens
    (4, 5),   # Stockholm and Athens
    (5, 6)    # Athens and Vilnius
]

# For each consecutive pair in the itinerary, add a constraint that the two cities must be connected by a direct flight.
def flight_constraint(a, b):
    # a and b are Z3 expressions representing city indices.
    conds = []
    for (x, y) in allowed_flights:
        conds.append(And(a == x, b == y))
        conds.append(And(a == y, b == x))
    return Or(*conds)

# We already know:
# Segment 0 (Berlin) -> Segment 1 (Barcelona): must be connected.
solver.add(flight_constraint(itinerary[0], itinerary[1]))
# Segment 1 (Barcelona) -> Segment 2 (Lyon): must be connected.
solver.add(flight_constraint(itinerary[1], itinerary[2]))
# Segment 2 (Lyon) -> Segment 3 (Nice): must be connected.
solver.add(flight_constraint(itinerary[2], itinerary[3]))

# Now constrain the order of the remaining three segments (positions 4, 5, 6).
# From Nice (3) at position 3, the next city (position 4) must be directly reachable from Nice.
# Nice is connected to Athens (5) and Stockholm (4) (but not Vilnius (6)).
# It turns out that the only ordering that will allow all remaining flight legs to work is:
# position 4 = Stockholm (4), position 5 = Athens (5) and then position 6 = Vilnius (6).
solver.add(itinerary[4] == 4)
solver.add(itinerary[5] == 5)
solver.add(itinerary[6] == 6)

# And add flight constraints for the remaining transitions:
solver.add(flight_constraint(itinerary[3], itinerary[4]))  # Nice -> Stockholm
solver.add(flight_constraint(itinerary[4], itinerary[5]))  # Stockholm -> Athens
solver.add(flight_constraint(itinerary[5], itinerary[6]))  # Athens -> Vilnius

# If we reach here, the following chain is forced by the constraints:
# Position:  City (duration)   Interval (start_day to end_day)
#    0:    Berlin (3)         [1, 3]          -> Conference on day 1 and day 3.
#    1:    Barcelona (2)      [3, 4]          -> Workshop between day 3 and day 4.
#    2:    Lyon (2)           [4, 5]          -> Wedding between day 4 and day 5.
#    3:    Nice (5)           [5, 9]
#    4:    Stockholm (5)      [9, 13]
#    5:    Athens (5)         [13, 17]
#    6:    Vilnius (4)        [17, 20]

if solver.check() == sat:
    model = solver.model()
    itinerary_plan = []
    for i in range(7):
        # Get the city index from the itinerary
        city_index = model[itinerary[i]].as_long()
        # Determine the start day for this segment.
        s_day = model[start[i]].as_long()
        # The end day is computed as start_day + duration - 1.
        e_day = s_day + durations[cities[city_index]] - 1
        itinerary_plan.append({
            "city": cities[city_index],
            "start_day": s_day,
            "end_day": e_day
        })
    output = {"itinerary": itinerary_plan}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")