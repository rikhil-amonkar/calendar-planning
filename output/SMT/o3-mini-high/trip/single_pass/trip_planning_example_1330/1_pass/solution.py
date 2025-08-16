from z3 import *
import json

# Mapping city id to name:
city_names = {
    0: "Salzburg", 
    1: "Venice", 
    2: "Bucharest", 
    3: "Brussels", 
    4: "Hamburg", 
    5: "Copenhagen", 
    6: "Nice", 
    7: "Zurich", 
    8: "Naples"
}

# Duration (in days) you plan to spend in each city.
# (Remember: if you fly on the last day of a stay, that day counts for both cities.)
# These values come from the problem statement.
durations = {
    0: 2,  # Salzburg
    1: 5,  # Venice
    2: 4,  # Bucharest
    3: 2,  # Brussels
    4: 4,  # Hamburg
    5: 4,  # Copenhagen
    6: 3,  # Nice
    7: 5,  # Zurich
    8: 4   # Naples
}

# Allowed direct flight connections (bidirectional)
allowed_flights = [
    (7, 3),  # Zurich <-> Brussels
    (2, 5),  # Bucharest <-> Copenhagen
    (1, 3),  # Venice <-> Brussels
    (6, 7),  # Nice <-> Zurich
    (4, 6),  # Hamburg <-> Nice
    (7, 8),  # Zurich <-> Naples
    (4, 2),  # Hamburg <-> Bucharest
    (7, 5),  # Zurich <-> Copenhagen
    (2, 3),  # Bucharest <-> Brussels
    (4, 3),  # Hamburg <-> Brussels
    (1, 8),  # Venice <-> Naples
    (1, 5),  # Venice <-> Copenhagen
    (2, 8),  # Bucharest <-> Naples
    (4, 5),  # Hamburg <-> Copenhagen
    (1, 7),  # Venice <-> Zurich
    (6, 3),  # Nice <-> Brussels
    (4, 1),  # Hamburg <-> Venice
    (5, 8),  # Copenhagen <-> Naples
    (6, 8),  # Nice <-> Naples
    (4, 7),  # Hamburg <-> Zurich
    (0, 4),  # Salzburg <-> Hamburg
    (7, 2),  # Zurich <-> Bucharest
    (3, 8),  # Brussels <-> Naples
    (5, 3),  # Copenhagen <-> Brussels
    (1, 6),  # Venice <-> Nice
    (6, 5)   # Nice <-> Copenhagen
]

# Helper: returns a Z3 "if-then-else" expression for the duration in a given city.
def get_duration(city):
    return If(city == 0, durations[0],
           If(city == 1, durations[1],
           If(city == 2, durations[2],
           If(city == 3, durations[3],
           If(city == 4, durations[4],
           If(city == 5, durations[5],
           If(city == 6, durations[6],
           If(city == 7, durations[7],
           If(city == 8, durations[8], 0)))))))))

# Create the solver instance.
s = Solver()

nCities = 9  # number of segments = number of cities (each visited exactly once)

# order[i] is the city index visited in segment i.
order = [Int("order_%d" % i) for i in range(nCities)]
for o in order:
    s.add(o >= 0, o <= 8)
s.add(Distinct(order))

# start[i] is the (symbolic) start day of segment i.
start = [Int("start_%d" % i) for i in range(nCities)]
s.add(start[0] == 1)  # trip always starts on day 1

# For each segment i (except the last), enforce: 
# start[i+1] = start[i] + (duration in city order[i]) - 1.
# (The -1 encodes that the flight day is counted for both cities.)
for i in range(nCities - 1):
    s.add(start[i+1] == start[i] + get_duration(order[i]) - 1)

# The final segment must end on day 25.
# i.e., start[last] + duration(last) - 1 == 25.
s.add(start[nCities-1] + get_duration(order[nCities-1]) - 1 == 25)

# Flight connectivity constraints:
# For every consecutive pair of segments, the cities must be connected by a direct flight.
for i in range(nCities - 1):
    flight_options = []
    for (a, b) in allowed_flights:
        # Either flight goes from a to b or from b to a.
        flight_options.append(And(order[i] == a, order[i+1] == b))
        flight_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(flight_options))
    
# Event time-window constraints.
# 1. Meet friends in Brussels between day 21 and day 22:
#    Brussels (id 3) is 2 days long and so its segment [start, start+1] must cover 21 or 22.
for i in range(nCities):
    s.add(Implies(order[i] == 3, 
                  Or(And(start[i] <= 21, start[i] + 1 >= 21),
                     And(start[i] <= 22, start[i] + 1 >= 22))))

# 2. Attend wedding in Copenhagen between day 18 and day 21:
#    Copenhagen (id 5) lasts 4 days so its segment [start, start+3] must cover at least one day in [18,21].
for i in range(nCities):
    s.add(Implies(order[i] == 5, And(start[i] <= 21, start[i] + 3 >= 18)))

# 3. Visit relatives in Nice between day 9 and day 11:
#    Nice (id 6) lasts 3 days so its segment [start, start+2] must include a day in [9,11].
for i in range(nCities):
    s.add(Implies(order[i] == 6, And(start[i] <= 11, start[i] + 2 >= 9)))

# 4. Attend workshop in Naples between day 22 and day 25:
#    Naples (id 8) lasts 4 days so its segment [start, start+3] must include a day in [22,25].
for i in range(nCities):
    s.add(Implies(order[i] == 8, And(start[i] <= 25, start[i] + 3 >= 22)))

# Solve the model.
if s.check() == sat:
    m = s.model()
    itinerary_segments = []
    for i in range(nCities):
        city_id = m.evaluate(order[i]).as_long()
        seg_start = m.evaluate(start[i]).as_long()
        dur = durations[city_id]
        seg_end = seg_start + dur - 1  # flight day counted in both segments
        itinerary_segments.append({
            "city": city_names[city_id],
            "days": f"{seg_start}-{seg_end}"
        })
    result = {"itinerary": itinerary_segments}
else:
    result = {"itinerary": "No solution found"}

print(json.dumps(result, indent=2))