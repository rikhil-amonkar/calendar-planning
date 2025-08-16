from z3 import *
import json

# --- Data definitions ---
# City indices and durations:
# 0: Valencia (2 days, must meet friend between day 3 and 4)
# 1: Oslo     (3 days, must meet friend between day 13 and 15)
# 2: Lyon     (4 days)
# 3: Prague   (3 days)
# 4: Paris    (4 days)
# 5: Nice     (4 days)
# 6: Seville  (5 days, must cover the show from day 5 to 9)
# 7: Tallinn  (2 days)
# 8: Mykonos  (5 days, wedding between day 21 and 25)
# 9: Lisbon   (2 days)
city_names = ["Valencia", "Oslo", "Lyon", "Prague", "Paris", "Nice", "Seville", "Tallinn", "Mykonos", "Lisbon"]
durations = {0:2, 1:3, 2:4, 3:3, 4:4, 5:4, 6:5, 7:2, 8:5, 9:2}

# Helper: given a Z3 expression x representing a city from 0 to 9, return its duration.
def get_duration(x):
    return If(x == 0, 2,
           If(x == 1, 3,
           If(x == 2, 4,
           If(x == 3, 3,
           If(x == 4, 4,
           If(x == 5, 4,
           If(x == 6, 5,
           If(x == 7, 2,
           If(x == 8, 5,
           If(x == 9, 2, 0))))))))))

# --- Create solver and decision variables ---
s = Solver()

# Create an array P[0..9] representing the order in which the 10 cities are visited.
P = [Int(f"P{i}") for i in range(10)]
for i in range(10):
    # Each P[i] is an integer between 0 and 9.
    s.add(P[i] >= 0, P[i] < 10)
s.add(Distinct(P))

# Create s_vars[0..9] as the start day for the visit of the city in position i.
S_vars = [Int(f"s{i}") for i in range(10)]
# The trip starts on day 1.
s.add(S_vars[0] == 1)

# For each city in position i, its “finish day” f_i is s[i] + duration - 1.
# And the overlapping flight rule forces the next city’s start day to equal the previous city’s finish day.
for i in range(9):
    s.add(S_vars[i+1] == S_vars[i] + get_duration(P[i]) - 1)
# The last city must finish on day 25.
s.add(S_vars[9] + get_duration(P[9]) - 1 == 25)

# --- Direct-flight connectivity constraints ---
# (Each pair (A,B) below represents a bidirectional direct flight.)
allowed_flights = [
    (9,4), (4,9),           # Lisbon ↔ Paris
    (2,5), (5,2),           # Lyon ↔ Nice
    (7,1), (1,7),           # Tallinn ↔ Oslo
    (3,2), (2,3),           # Prague ↔ Lyon
    (4,1), (1,4),           # Paris ↔ Oslo
    (9,6), (6,9),           # Lisbon ↔ Seville
    (3,9), (9,3),           # Prague ↔ Lisbon
    (1,5), (5,1),           # Oslo ↔ Nice
    (0,4), (4,0),           # Valencia ↔ Paris
    (0,9), (9,0),           # Valencia ↔ Lisbon
    (4,5), (5,4),           # Paris ↔ Nice
    (5,8), (8,5),           # Nice ↔ Mykonos
    (4,2), (2,4),           # Paris ↔ Lyon
    (0,2), (2,0),           # Valencia ↔ Lyon
    (3,1), (1,3),           # Prague ↔ Oslo
    (3,4), (4,3),           # Prague ↔ Paris
    (6,4), (4,6),           # Seville ↔ Paris
    (1,2), (2,1),           # Oslo ↔ Lyon
    (3,0), (0,3),           # Prague ↔ Valencia
    (9,5), (5,9),           # Lisbon ↔ Nice
    (9,1), (1,9),           # Lisbon ↔ Oslo
    (0,6), (6,0),           # Valencia ↔ Seville
    (9,2), (2,9),           # Lisbon ↔ Lyon
    (4,7), (7,4),           # Paris ↔ Tallinn
    (3,7), (7,3)            # Prague ↔ Tallinn
]
# For every consecutive city pair in the order, enforce that the direct flight exists.
for i in range(9):
    # Build a disjunction of all allowed pairs.
    s.add(Or([And(P[i] == a, P[i+1] == b) for (a,b) in allowed_flights]))

# --- Special event constraints ---
# (They “force” the visit interval for the city with a special requirement to cover a given day or interval.)
for i in range(10):
    # If the city is Valencia, then its start day S_vars[i] must lie between 2 and 4
    s.add(Implies(P[i] == 0, And(S_vars[i] >= 2, S_vars[i] <= 4)))
    # If the city is Oslo, then its start day must be between 11 and 15
    s.add(Implies(P[i] == 1, And(S_vars[i] >= 11, S_vars[i] <= 15)))
    # If the city is Seville, then it must start exactly on day 5 (so that day 5–9 are in Seville)
    s.add(Implies(P[i] == 6, S_vars[i] == 5))
    # If the city is Mykonos, then its start day must be between 17 and 21
    s.add(Implies(P[i] == 8, And(S_vars[i] >= 17, S_vars[i] <= 21)))

# --- Solve the model ---
if s.check() == sat:
    m = s.model()
    # Retrieve the order in which the cities are visited.
    order = [m.evaluate(P[i]).as_long() for i in range(10)]
    s_values = [m.evaluate(S_vars[i]).as_long() for i in range(10)]
    # For convenience, compute the (classical) finish time for each visited city:
    duration_values = [durations[order[i]] for i in range(10)]
    finish_times = [s_values[i] + duration_values[i] - 1 for i in range(10)]
    
    # --- Build the day-by-day itinerary ---
    # We interpret the rules as follows:
    # (1) The first city (position 0) has “full days” from day 1 up to (but not including) the flight day.
    # (2) For each later city the flight day (i.e. the start day S_vars[i]) is associated with the arriving city.
    # Thus, the itinerary for day d (1≤d≤25) is that city whose start day is the greatest S_vars[i] that does not exceed d.
    itinerary = []
    for d in range(1, 26):
        chosen_segment = None
        max_start = -1
        for i in range(10):
            si = s_values[i]
            if si <= d and si > max_start:
                max_start = si
                chosen_segment = i
        # The city “visited” on day d is the one assigned at the chosen segment.
        city_index = order[chosen_segment]
        itinerary.append({"day": d, "place": city_names[city_index]})
    
    # Output the itinerary as a JSON–formatted dictionary.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")