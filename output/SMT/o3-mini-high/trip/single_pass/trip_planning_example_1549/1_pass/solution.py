from z3 import *

# --- Data definitions ---

# We label the 10 cities with indices:
# 0: Prague (5 days)
# 1: Tallinn (3 days)   -- must include at least one day between 18 and 20 (i.e. the interval [S, S+2] intersects {18,19,20})
# 2: Warsaw (2 days)
# 3: Porto (3 days)
# 4: Naples (5 days)
# 5: Milan (3 days)     -- must include at least one day between 24 and 26 (i.e. the interval [S, S+2] intersects {24,25,26})
# 6: Lisbon (5 days)
# 7: Santorini (5 days)
# 8: Riga (4 days)      -- must be entered on day 5 so that the 4‐day show from day 5 to day 8 is fully attended
# 9: Stockholm (2 days)

durations = [5, 3, 2, 3, 5, 3, 5, 5, 4, 2]
city_names = ["Prague", "Tallinn", "Warsaw", "Porto", "Naples",
              "Milan", "Lisbon", "Santorini", "Riga", "Stockholm"]

# --- Allowed Flight Connections ---
# (Note: when flying from A to B on day X, that day counts toward both cities.)
# Allowed direct flights (interpreting “and” as bidirectional except when a directed arrow is mentioned):
#
# • Riga <-> Prague
# • Stockholm <-> Milan
# • Riga <-> Milan
# • Lisbon <-> Stockholm
# • Stockholm -> Santorini     (only from Stockholm to Santorini)
# • Naples <-> Warsaw
# • Lisbon <-> Warsaw
# • Naples <-> Milan
# • Lisbon <-> Naples
# • Riga -> Tallinn            (only from Riga to Tallinn)
# • Tallinn <-> Prague
# • Stockholm <-> Warsaw
# • Riga <-> Warsaw
# • Lisbon <-> Riga
# • Riga <-> Stockholm
# • Lisbon <-> Porto
# • Lisbon <-> Prague
# • Milan <-> Porto
# • Prague <-> Milan
# • Lisbon <-> Milan
# • Warsaw <-> Porto
# • Warsaw <-> Tallinn
# • Santorini <-> Milan
# • Stockholm <-> Prague
# • Stockholm <-> Tallinn
# • Warsaw <-> Milan
# • Santorini <-> Naples
# • Warsaw <-> Prague

# We separate the two “directed‐only” flights:
directed_edges = [(9, 7),   # Stockholm -> Santorini
                  (8, 1)]   # Riga -> Tallinn
# And now list the symmetric (bidirectional) pairs (we list one orientation, and later add both directions):
symmetric_edges = {
    (8, 0),  # Riga - Prague
    (9, 5),  # Stockholm - Milan
    (8, 5),  # Riga - Milan
    (6, 9),  # Lisbon - Stockholm
    (4, 2),  # Naples - Warsaw
    (6, 2),  # Lisbon - Warsaw
    (4, 5),  # Naples - Milan
    (6, 4),  # Lisbon - Naples
    (1, 0),  # Tallinn - Prague
    (9, 2),  # Stockholm - Warsaw
    (8, 2),  # Riga - Warsaw
    (6, 8),  # Lisbon - Riga
    (8, 9),  # Riga - Stockholm
    (6, 3),  # Lisbon - Porto
    (6, 0),  # Lisbon - Prague
    (5, 3),  # Milan - Porto
    (6, 5),  # Lisbon - Milan
    (2, 3),  # Warsaw - Porto
    (2, 1),  # Warsaw - Tallinn
    (7, 5),  # Santorini - Milan
    (9, 0),  # Stockholm - Prague
    (9, 1),  # Stockholm - Tallinn
    (2, 5),  # Warsaw - Milan
    (7, 4),  # Santorini - Naples
    (2, 0)   # Warsaw - Prague
}
# For each symmetric edge we add both directions.
sym_allowed = []
for (a, b) in symmetric_edges:
    sym_allowed.append((a, b))
    sym_allowed.append((b, a))
# The full allowed set is then:
allowed_set = set(directed_edges) | set(sym_allowed)

# --- Z3 model setup ---

s = Solver()

# We will decide an ordering of the cities in the trip.
# order[i] is the city index visited at itinerary position i (0-based, total 10 positions).
order = [Int(f"order_{i}") for i in range(10)]
for o in order:
    s.add(o >= 0, o < 10)
s.add(Distinct(order))

# S[i] will be the start day on which we "enter" the city at itinerary position i.
# (Recall: if you fly from city A to city B on day X, you count day X for both.)
S_days = [Int(f"S_{i}") for i in range(10)]

# The trip must last exactly 28 days.
# When staying in a city c with duration d, if you start on day S then you are there on days S, S+1, …, S+d-1.
# Also note: For consecutive cities i, i+1 we require S[i+1] = S[i] + (duration of city_i) - 1.
s.add(S_days[0] == 1)  # Trip starts on day 1.

for i in range(9):
    # Use nested if-then-else to pick the proper duration based on the city in order[i]
    dur_expr = If(order[i] == 0, durations[0],
              If(order[i] == 1, durations[1],
              If(order[i] == 2, durations[2],
              If(order[i] == 3, durations[3],
              If(order[i] == 4, durations[4],
              If(order[i] == 5, durations[5],
              If(order[i] == 6, durations[6],
              If(order[i] == 7, durations[7],
              If(order[i] == 8, durations[8],
              If(order[i] == 9, durations[9],
                 0)))))))))
    s.add(S_days[i+1] == S_days[i] + dur_expr - 1)

# The final city must finish on day 28.
dur_last = If(order[9] == 0, durations[0],
           If(order[9] == 1, durations[1],
           If(order[9] == 2, durations[2],
           If(order[9] == 3, durations[3],
           If(order[9] == 4, durations[4],
           If(order[9] == 5, durations[5],
           If(order[9] == 6, durations[6],
           If(order[9] == 7, durations[7],
           If(order[9] == 8, durations[8],
           If(order[9] == 9, durations[9], 0)))))))))
s.add(S_days[9] + dur_last - 1 == 28)

# --- Flight connectivity constraints ---
# For every consecutive pair (order[i], order[i+1]), there must be a direct flight.
for i in range(9):
    conds = []
    for (a, b) in allowed_set:
        conds.append(And(order[i] == a, order[i+1] == b))
    s.add(Or(conds))

# --- Special scheduling constraints ---

# (1) Riga (city 8) must be scheduled so that you attend the annual show from Day 5 to Day 8.
# Given the stay in Riga is 4 days, the only possibility to cover days 5-8 is to enter on day 5.
for i in range(10):
    s.add(Implies(order[i] == 8, S_days[i] == 5))

# (2) In Tallinn (city 1, 3-day stay) you plan to visit relatives between day 18 and day 20.
# We require that the interval [S, S+2] (for a 3-day stay) has a nonempty intersection with {18, 19, 20}.
# A simple sufficient condition is: S <= 20 and S+2 >= 18.
for i in range(10):
    s.add(Implies(order[i] == 1, And(S_days[i] <= 20, S_days[i] + 2 >= 18)))

# (3) In Milan (city 5, 3-day stay) you want to meet a friend between day 24 and day 26.
# So require that [S, S+2] intersects [24,26]: i.e. S <= 26 and S+2 >= 24.
for i in range(10):
    s.add(Implies(order[i] == 5, And(S_days[i] <= 26, S_days[i] + 2 >= 24)))

# (Optional) Bound all start days between 1 and 28.
for i in range(10):
    s.add(And(S_days[i] >= 1, S_days[i] <= 28))

# --- Solve and output the itinerary ---

if s.check() == sat:
    m = s.model()
    # Retrieve the order and start days
    order_vals = [m[order[i]].as_long() for i in range(10)]
    S_vals = [m[S_days[i]].as_long() for i in range(10)]
    
    # For each itinerary position, compute the city interval [start, end]:
    itinerary_segments = []
    for i in range(10):
        city = order_vals[i]
        start_day = S_vals[i]
        dur = durations[city]
        end_day = start_day + dur - 1
        itinerary_segments.append((city, start_day, end_day))
    
    # For the output we must provide a day-by-day mapping.
    # On flight days the day counts for both the city you are leaving and the city you are arriving.
    # We'll compute for each day 1..28 the set of cities (by name) where you are “present”.
    day_locations = {day: [] for day in range(1, 29)}
    for (city, start_day, end_day) in itinerary_segments:
        for day in range(start_day, end_day + 1):
            if city_names[city] not in day_locations[day]:
                day_locations[day].append(city_names[city])
    
    # Build a list of day mappings (sorted by day)
    itinerary_output = []
    for day in range(1, 29):
        itinerary_output.append({
            "day": day,
            "locations": day_locations[day]
        })
    
    import json
    print(json.dumps({"itinerary": itinerary_output}, indent=2))
else:
    print("No solution found")