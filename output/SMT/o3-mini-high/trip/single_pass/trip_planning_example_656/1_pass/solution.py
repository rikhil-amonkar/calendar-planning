from z3 import *
import json

# We have 6 cities.
# We assign each city an integer code as follows:
# 0: Reykjavik (5 days)
# 1: Istanbul   (4 days) - must include a day between 5 and 8 (friends meeting)
# 2: Edinburgh  (5 days)
# 3: Oslo       (2 days) - must include a day between 8 and 9 (relatives visit)
# 4: Stuttgart  (3 days)
# 5: Bucharest  (5 days)

city_names = {
    0: "Reykjavik",
    1: "Istanbul",
    2: "Edinburgh",
    3: "Oslo",
    4: "Stuttgart",
    5: "Bucharest"
}

# Fixed durations by city index:
durations = {
    0: 5,
    1: 4,
    2: 5,
    3: 2,
    4: 3,
    5: 5
}

# Allowed direct-flight transitions.
# (Note: all connections are two‐way “except” the Reykjavik–Stuttgart connection which is only allowed 
# in the direction: Reykjavik -> Stuttgart.)
allowed_transitions = {
    0: [3, 4],        # From Reykjavik you can fly to Oslo (3) or Stuttgart (4)
    1: [3, 2, 4, 5],   # Istanbul: can fly to Oslo, Edinburgh, Stuttgart, Bucharest
    2: [4, 1, 3],      # Edinburgh: can fly to Stuttgart, Istanbul, Oslo
    3: [5, 1, 0, 2],   # Oslo: can fly to Bucharest, Istanbul, Reykjavik, Edinburgh
    4: [1, 2],        # Stuttgart: can fly to Istanbul or Edinburgh (note: cannot fly back to Reykjavik)
    5: [3, 1]         # Bucharest: can fly to Oslo or Istanbul
}

# There are 6 city segments that together (after subtracting the overlapping flight days) cover 19 days.
n = 6

# Create Z3 solver
s = Solver()

# Create an array of Int variables for the city order:
cities = [Int("city_%d" % i) for i in range(n)]
# Each city must be one of the 0..5 and they all must be distinct.
for i in range(n):
    s.add(And(cities[i] >= 0, cities[i] <= 5))
s.add(Distinct(cities))

# Create an array of Int variables for the start day of each city segment.
# By convention, S[0] = day 1.
S_days = [Int("S_%d" % i) for i in range(n)]
s.add(S_days[0] == 1)
# Also, each start day must be at least 1.
for i in range(n):
    s.add(S_days[i] >= 1)

# Helper: given a city variable (which is an Int) return its duration as a Z3 expression.
def duration_expr(city_var):
    return If(city_var == 0, durations[0],
           If(city_var == 1, durations[1],
           If(city_var == 2, durations[2],
           If(city_var == 3, durations[3],
           If(city_var == 4, durations[4],
              durations[5]))))) 

# The segments follow consecutively.
for i in range(n - 1):
    # When you fly on day X from city A to city B:
    #   The departure (city A) counts day X and the arrival (city B) also counts day X.
    # Therefore: S[i+1] = S[i] + (duration of city[i]) - 1.
    s.add(S_days[i+1] == S_days[i] + duration_expr(cities[i]) - 1)

# The last city must end on day 19.
# End day for segment i is S_days[i] + duration_expr(cities[i]) - 1.
s.add(S_days[n-1] + duration_expr(cities[n-1]) - 1 == 19)

# Add the flight (transition) constraints.
# For each consecutive pair, the allowed transitions depend on the current city.
for i in range(n - 1):
    # For each possible city code c for cities[i], impose that cities[i+1] is one of allowed_transitions[c].
    transition_clauses = []
    for c in range(6):
        allowed_next = allowed_transitions[c]
        clause = Implies(cities[i] == c, Or([cities[i+1] == next_city for next_city in allowed_next]))
        transition_clauses.append(clause)
    s.add(And(transition_clauses))

# Add the extra calendaring (meeting) constraints.
# Istanbul (city code 1) must include at least one day between day 5 and day 8.
for i in range(n):
    # If this segment is Istanbul, then its interval [S_days[i], S_days[i] + durations[1] - 1] must overlap [5,8].
    s.add(Implies(cities[i] == 1, And(S_days[i] <= 8, S_days[i] + durations[1] - 1 >= 5)))
    
# Oslo (city code 3) must include at least one day between day 8 and day 9.
for i in range(n):
    s.add(Implies(cities[i] == 3, And(S_days[i] <= 9, S_days[i] + durations[3] - 1 >= 8)))

# Solve the constraints.
if s.check() == sat:
    m = s.model()
    # Read the solution. Compute the segment intervals.
    itinerary_segments = []
    for i in range(n):
        c = m.evaluate(cities[i]).as_long()
        start_day = m.evaluate(S_days[i]).as_long()
        dur = durations[c]
        end_day = start_day + dur - 1
        itinerary_segments.append({
            "city": city_names[c],
            "start": start_day,
            "end": end_day
        })
    
    # Build a full day-by-day itinerary.
    # A day may be “covered” by two segments if it is the flight overlap day.
    day_itinerary = []
    for d in range(1, 20):  # days 1 through 19
        places = []
        for seg in itinerary_segments:
            if seg["start"] <= d <= seg["end"]:
                places.append(seg["city"])
        day_itinerary.append({"day": d, "places": places})
    
    # Prepare final result as a JSON-formatted dictionary.
    result = {"itinerary": day_itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")