from z3 import Solver, Int, If, And, Or, Implies, Distinct, sat
import json

# --- Data Setup ---

# Map each city to an id.
name_to_id = {
    "Warsaw": 0,
    "Porto": 1,
    "Naples": 2,
    "Brussels": 3,
    "Split": 4,
    "Reykjavik": 5,
    "Amsterdam": 6,
    "Helsinki": 7,
    "Lyon": 8,
    "Valencia": 9
}
id_to_name = {v: k for k, v in name_to_id.items()}

# Fixed durations for each city
# Warsaw: 3, Porto: 5, Naples: 4, Brussels: 3, Split: 3,
# Reykjavik: 5, Amsterdam: 4, Helsinki: 4, Lyon: 3, Valencia: 2
durations = {
    0: 3,
    1: 5,
    2: 4,
    3: 3,
    4: 3,
    5: 5,
    6: 4,
    7: 4,
    8: 3,
    9: 2
}

# List of flights given as pairs (using city names).
# We assume direct flights are bidirectional.
given_flights = [
    ("Amsterdam", "Warsaw"),
    ("Helsinki", "Brussels"),
    ("Helsinki", "Warsaw"),
    ("Reykjavik", "Brussels"),
    ("Amsterdam", "Lyon"),
    ("Amsterdam", "Naples"),
    ("Amsterdam", "Reykjavik"),
    ("Naples", "Valencia"),
    ("Porto", "Brussels"),
    ("Amsterdam", "Split"),
    ("Lyon", "Split"),
    ("Warsaw", "Split"),
    ("Porto", "Amsterdam"),
    ("Helsinki", "Split"),
    ("Brussels", "Lyon"),
    ("Porto", "Lyon"),
    ("Reykjavik", "Warsaw"),
    ("Brussels", "Valencia"),
    ("Valencia", "Lyon"),
    ("Porto", "Warsaw"),
    ("Warsaw", "Valencia"),
    ("Amsterdam", "Helsinki"),
    ("Porto", "Valencia"),
    ("Warsaw", "Brussels"),
    ("Warsaw", "Naples"),
    ("Naples", "Split"),
    ("Helsinki", "Naples"),
    ("Helsinki", "Reykjavik"),
    ("Amsterdam", "Valencia"),
    ("Naples", "Brussels")
]

# Convert flight list to a set of id pairs, adding both directions.
flight_edges = set()
for (c1, c2) in given_flights:
    a = name_to_id[c1]
    b = name_to_id[c2]
    flight_edges.add((a, b))
    flight_edges.add((b, a))
# Convert to list form (for later Or constraints)
flight_edges = list(flight_edges)

# --- Z3 Model Setup ---

# We have 10 positions (slots) in our itinerary.
solver = Solver()

# itinerary[i] will be the city (by id) visited in slot i (i=0,...,9)
itinerary = [Int(f"city_{i}") for i in range(10)]
# start[i] will be the start day (an integer between 1 and 27) for the block in slot i
start = [Int(f"start_{i}") for i in range(10)]

# Add domain constraints for itinerary cities: they should be between 0 and 9.
for i in range(10):
    solver.add(itinerary[i] >= 0, itinerary[i] <= 9)
# They must be all different.
solver.add(Distinct(itinerary))

# Helper: duration function as a Z3 expression based on the city id.
def dur(city):
    return If(city == 0, 3,
           If(city == 1, 5,
           If(city == 2, 4,
           If(city == 3, 3,
           If(city == 4, 3,
           If(city == 5, 5,
           If(city == 6, 4,
           If(city == 7, 4,
           If(city == 8, 3,
           If(city == 9, 2, 0))))))))))

# The first day is fixed.
solver.add(start[0] == 1)

# If we fly from city in slot i to the next city in slot i+1,
# the flight day (which is s[i] + duration(city)-1) is the overlapping day,
# and in our model the next city’s visit begins exactly on that day.
for i in range(1, 10):
    solver.add(start[i] == start[i-1] + dur(itinerary[i-1]) - 1)

# The overall itinerary uses 27 days.
# The last city’s block runs from start[9] through start[9] + duration - 1.
solver.add(start[9] + dur(itinerary[9]) - 1 == 27)

# --- Add Flight Constraints ---
# For every consecutive pair in the itinerary, there must be a direct flight.
for i in range(9):
    possible_edges = []
    for (a, b) in flight_edges:
        possible_edges.append(And(itinerary[i] == a, itinerary[i+1] == b))
    solver.add(Or(possible_edges))

# --- Add Event & Time-Window Constraints ---
# Note: When a flight is taken on a day, that day counts in both cities.
#
# Event: In Porto (id 1, duration=5) you must attend a workshop between day 1 and day 5.
# So Porto’s block [start, start+4] must include at least one day in [1,5]:
#   start <= 5 <= start+4.
for i in range(10):
    solver.add(Implies(itinerary[i] == name_to_id["Porto"],
                       And(start[i] <= 5, start[i] + 4 >= 5)))

# Event: In Naples (id 2, duration=4) you must attend a conference on day 17 and day 20.
# For a 4‐day stay these days will both be included only if the block is exactly day 17–20.
for i in range(10):
    solver.add(Implies(itinerary[i] == name_to_id["Naples"],
                       start[i] == 17))

# Event: In Brussels (id 3, duration=3) you must attend a show from day 20 to 22.
# That forces the block to be exactly day 20–22.
for i in range(10):
    solver.add(Implies(itinerary[i] == name_to_id["Brussels"],
                       start[i] == 20))

# Event: In Amsterdam (id 6, duration=4) you visit relatives between day 5 and day 8.
# So its block [start, start+3] must overlap [5,8]:
#   start <= 8 and start+3 >= 5.
for i in range(10):
    solver.add(Implies(itinerary[i] == name_to_id["Amsterdam"],
                       And(start[i] <= 8, start[i] + 3 >= 5)))

# Event: In Helsinki (id 7, duration=4) you attend a wedding between day 8 and day 11.
# So its block [start, start+3] must overlap [8,11]:
#   start <= 11 and start+3 >= 8.
for i in range(10):
    solver.add(Implies(itinerary[i] == name_to_id["Helsinki"],
                       And(start[i] <= 11, start[i] + 3 >= 8)))

# --- Solve the Model ---
if solver.check() == sat:
    model = solver.model()
    # Build a list of itinerary segments.
    # Each segment is a city visited starting at day s until (s + duration - 1)
    itinerary_segments = []
    for i in range(10):
        city_id = model[itinerary[i]].as_long()
        city_name = id_to_name[city_id]
        s_day = model[start[i]].as_long()
        dur_val = durations[city_id]
        e_day = s_day + dur_val - 1
        itinerary_segments.append({
            "city": city_name,
            "start_day": s_day,
            "end_day": e_day
        })
    # Prepare the final JSON dictionary.
    output = {"itinerary": itinerary_segments}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")