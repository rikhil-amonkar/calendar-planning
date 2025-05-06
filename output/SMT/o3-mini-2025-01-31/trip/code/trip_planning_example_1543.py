from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 10 cities with the following properties:
# 0: Prague     - 3 days, with a workshop that must be attended between day 1 and day 3.
#                  (For a 3-day visit [S, S+2] to include at least one day in {1,2,3}, we require S ≤ 3.)
# 1: Warsaw     - 4 days, and you want to meet friends there between day 20 and day 23.
#                  (For a 4-day visit [S, S+3] to overlap [20,23], require S ≤ 23 and S+3 ≥ 20.)
# 2: Dublin     - 3 days.
# 3: Athens     - 3 days.
# 4: Vilnius    - 4 days.
# 5: Porto      - 5 days, with a conference that you must attend during day 16 and day 20.
#                  (For a 5-day visit [S, S+4] to include both day 16 and day 20, require S ≤ 16 and S+4 ≥ 20.)
# 6: London     - 3 days, with a wedding between day 3 and day 5.
#                  (For a 3-day visit [S, S+2] to overlap [3,5], require S ≤ 5 and S+2 ≥ 3.)
# 7: Seville    - 2 days.
# 8: Lisbon     - 5 days, with relatives to visit between day 5 and day 9.
#                  (For a 5-day visit [S, S+4] to overlap [5,9], require S ≤ 9 and S+4 ≥ 5.)
# 9: Dubrovnik  - 3 days.
#
# Total durations = 3+4+3+3+4+5+3+2+5+3 = 35.
# With 10 cities, there are 9 flights; we "overlap" one day per flight.
# Thus, the effective trip length is 35 - 9 = 26 days.
# Therefore, the final departure day must equal 26.

# Allowed direct flights (bidirectional):
# - Warsaw and Vilnius       : (1,4) and (4,1)
# - Prague and Athens         : (0,3) and (3,0)
# - London and Lisbon         : (6,8) and (8,6)
# - Lisbon and Porto          : (8,5) and (5,8)
# - Prague and Lisbon         : (0,8) and (8,0)
# - London and Dublin         : (6,2) and (2,6)
# - Athens and Vilnius        : (3,4) and (4,3)
# - Athens and Dublin         : (3,2) and (2,3)
# - Prague and London         : (0,6) and (6,0)
# - London and Warsaw         : (6,1) and (1,6)
# - Dublin and Seville        : (2,7) and (7,2)
# - Seville and Porto         : (7,5) and (5,7)
# - Lisbon and Athens         : (8,3) and (3,8)
# - Dublin and Porto          : (2,5) and (5,2)
# - Athens and Warsaw         : (3,1) and (1,3)
# - Lisbon and Warsaw         : (8,1) and (1,8)
# - Porto and Warsaw          : (5,1) and (1,5)
# - Prague and Warsaw         : (0,1) and (1,0)
# - Prague and Dublin         : (0,2) and (2,0)
# - Athens and Dubrovnik      : (3,9) and (9,3)
# - Lisbon and Dublin         : (8,2) and (2,8)
# - Dubrovnik and Dublin      : (9,2) and (2,9)
# - Lisbon and Seville        : (8,7) and (7,8)
# - London and Athens         : (6,3) and (3,6)

cities = ["Prague", "Warsaw", "Dublin", "Athens", "Vilnius", "Porto", "London", "Seville", "Lisbon", "Dubrovnik"]
durations = [3, 4, 3, 3, 4, 5, 3, 2, 5, 3]
n = len(cities)
total_trip = 26

solver = Solver()

# Decision variables:
# pos[i] indicates the city (by index) visited in the i-th position.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] denotes the arrival day at the city at position i.
# The trip starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain the arrival times: when moving from city at pos[i-1] to pos[i],
# the arrival day of the latter is: S[i] = S[i-1] + (duration(city at pos[i-1]) - 1).
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The final departure day must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Define allowed flights between consecutive cities.
allowed_flights = {
    (1,4), (4,1),           # Warsaw <-> Vilnius
    (0,3), (3,0),           # Prague <-> Athens
    (6,8), (8,6),           # London <-> Lisbon
    (8,5), (5,8),           # Lisbon <-> Porto
    (0,8), (8,0),           # Prague <-> Lisbon
    (6,2), (2,6),           # London <-> Dublin
    (3,4), (4,3),           # Athens <-> Vilnius
    (3,2), (2,3),           # Athens <-> Dublin
    (0,6), (6,0),           # Prague <-> London
    (6,1), (1,6),           # London <-> Warsaw
    (2,7), (7,2),           # Dublin <-> Seville
    (7,5), (5,7),           # Seville <-> Porto
    (8,3), (3,8),           # Lisbon <-> Athens
    (2,5), (5,2),           # Dublin <-> Porto
    (3,1), (1,3),           # Athens <-> Warsaw
    (8,1), (1,8),           # Lisbon <-> Warsaw
    (5,1), (1,5),           # Porto <-> Warsaw
    (0,1), (1,0),           # Prague <-> Warsaw
    (0,2), (2,0),           # Prague <-> Dublin
    (3,9), (9,3),           # Athens <-> Dubrovnik
    (8,2), (2,8),           # Lisbon <-> Dublin
    (9,2), (2,9),           # Dubrovnik <-> Dublin
    (8,7), (7,8),           # Lisbon <-> Seville
    (6,3), (3,6)            # London <-> Athens
}

for i in range(n - 1):
    flight_options = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                flight_options.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(flight_options))

# Special event constraints:
for i in range(n):
    # For Prague (index 0): workshop between day 1 and day 3.
    solver.add(If(pos[i] == 0, S[i] <= 3, True))
    
    # For Warsaw (index 1): meet friends between day 20 and day 23.
    solver.add(If(pos[i] == 1, And(S[i] <= 23, S[i] + 3 >= 20), True))
    
    # For Porto (index 5): conference during day 16 and day 20.
    # To include both day 16 and day 20 in a 5-day visit [S, S+4], require S ≤ 16 and S+4 ≥ 20.
    solver.add(If(pos[i] == 5, And(S[i] <= 16, S[i] + 4 >= 20), True))
    
    # For London (index 6): wedding between day 3 and day 5.
    solver.add(If(pos[i] == 6, And(S[i] <= 5, S[i] + 2 >= 3), True))
    
    # For Lisbon (index 8): visit relatives between day 5 and day 9.
    solver.add(If(pos[i] == 8, And(S[i] <= 9, S[i] + 4 >= 5), True))

# -----------------------------------------------------------------------------
# Solve the model.
# -----------------------------------------------------------------------------
if solver.check() == sat:
    m = solver.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals  = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city_idx = itinerary[i]
        city = cities[city_idx]
        arrival = arrivals[i]
        departure = arrival + durations[city_idx] - 1
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")