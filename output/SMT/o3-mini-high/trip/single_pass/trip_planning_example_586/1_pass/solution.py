from z3 import *
import json

# We label the cities as follows:
#  0: Prague (2 days, and workshop between day 1 and 2 must be attended)
#  1: Helsinki (4 days, show must be attended from day 2 to day 5)
#  2: Frankfurt (3 days)
#  3: Naples (4 days)
#  4: Lyon (3 days)

# Required durations for each city:
durations = {
    0: 2,  # Prague
    1: 4,  # Helsinki
    2: 3,  # Frankfurt
    3: 4,  # Naples
    4: 3   # Lyon
}

# Allowed direct flight connections (bidirectional)
allowed_flights = [
    (0, 1), (1, 0),  # Prague <-> Helsinki
    (0, 2), (2, 0),  # Prague <-> Frankfurt
    (0, 4), (4, 0),  # Prague <-> Lyon
    (1, 2), (2, 1),  # Helsinki <-> Frankfurt
    (1, 3), (3, 1),  # Helsinki <-> Naples
    (2, 3), (3, 2),  # Frankfurt <-> Naples
    (2, 4), (4, 2)   # Frankfurt <-> Lyon
]

# A helper function to “lookup” the duration from an (integer) city variable.
def get_duration(city):
    return If(city == 0, durations[0],
           If(city == 1, durations[1],
           If(city == 2, durations[2],
           If(city == 3, durations[3],
              durations[4]))))  # city == 4

# Create the solver
s = Solver()

# We have 5 segments (each segment is a stay in one city)
num_segments = 5

# Each segment i gets assigned a city (an Int variable 0..4)
# We require that every city is visited exactly once.
seg = [Int("seg_%d" % i) for i in range(num_segments)]

# Force the workshop in Prague between day 1 and 2.
# We force Prague (0) to be visited in segment 0.
s.add(seg[0] == 0)
# The annual Helsinki show (days 2-5) forces Helsinki (1) to appear in segment 1.
s.add(seg[1] == 1)

# For the remaining segments (2,3,4), they must be a permutation of {2,3,4} -> {Frankfurt, Naples, Lyon}
for i in range(2, num_segments):
    s.add(Or(seg[i] == 2, seg[i] == 3, seg[i] == 4))
s.add(Distinct(seg))

# Create start time variables for each segment.
# The idea is that segment i runs from start[i] to end[i] = start[i] + (duration of seg[i]) - 1.
start = [Int("start_%d" % i) for i in range(num_segments)]

# The trip starts on Day 1.
s.add(start[0] == 1)

# For consecutive segments, the start of seg[i+1] equals the end of seg[i].
for i in range(num_segments - 1):
    # end time of segment i is: start[i] + get_duration(seg[i]) - 1.
    s.add(start[i+1] == start[i] + get_duration(seg[i]) - 1)

# Total trip must finish on Day 12.
s.add(start[num_segments - 1] + get_duration(seg[num_segments - 1]) - 1 == 12)

# Now add flight connectivity constraints.
# When flying from seg[i] to seg[i+1] (on the shared day), a direct flight must exist.
for i in range(num_segments - 1):
    a = seg[i]
    b = seg[i+1]
    # a valid transition (a, b) is one of the allowed flights.
    flight_ok = []
    for (c1, c2) in allowed_flights:
        flight_ok.append(And(a == c1, b == c2))
    s.add(Or(flight_ok))
    
# (At this point, note that the Helsinki show from day2 to day5 is “hard-wired” since:
#    seg[1] is Helsinki and its segment runs from day2 to day5, thanks to:
#       start[1] = start[0] + 2 - 1 = 2   and get_duration(Helsinki)=4, so end = 5.)
    
if s.check() == sat:
    m = s.model()
    # Retrieve the solved segments and start times
    seg_vals = [m.evaluate(seg[i]).as_long() for i in range(num_segments)]
    start_vals = [m.evaluate(start[i]).as_long() for i in range(num_segments)]
    
    # Calculate end times for each segment.
    ends = [start_vals[i] + durations[seg_vals[i]] - 1 for i in range(num_segments)]
    
    # Build a day-by-day itinerary.
    # On each day d from 1 to 12, if d falls in a segment's [start, end] then the visitor is in that city.
    # (On flight days the visitor will appear in two segments.)
    day_itinerary = {}
    for d in range(1, 13):
        places = []
        for i in range(num_segments):
            if start_vals[i] <= d <= ends[i]:
                # Map the integer back to city name.
                if seg_vals[i] == 0:
                    places.append("Prague")
                elif seg_vals[i] == 1:
                    places.append("Helsinki")
                elif seg_vals[i] == 2:
                    places.append("Frankfurt")
                elif seg_vals[i] == 3:
                    places.append("Naples")
                elif seg_vals[i] == 4:
                    places.append("Lyon")
        day_itinerary[d] = places

    # Build the JSON-formatted dictionary for output.
    itinerary_list = []
    for d in range(1, 13):
        itinerary_list.append({"day": d, "cities": day_itinerary[d]})
    
    output = {"itinerary": itinerary_list}
    print(json.dumps(output, indent=4))
else:
    print("No solution found.")