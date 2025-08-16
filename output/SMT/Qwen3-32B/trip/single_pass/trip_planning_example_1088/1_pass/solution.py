from z3 import *

# Define cities as integers
R = 0
ST = 1
O = 2
S = 3
Sp = 4
G = 5
P = 6
T = 7

durations = [2, 3, 5, 5, 3, 2, 3, 5]

# Define direct flights as a set of tuples (a, b)
direct_flights = set()
direct_flights.add((R, ST))
direct_flights.add((R, S))
direct_flights.add((R, T))
direct_flights.add((R, O))
direct_flights.add((ST, O))
direct_flights.add((ST, S))
direct_flights.add((ST, Sp))
direct_flights.add((ST, G))
direct_flights.add((O, Sp))
direct_flights.add((O, G))
direct_flights.add((O, T))
direct_flights.add((O, P))
direct_flights.add((S, R))
direct_flights.add((S, P))
direct_flights.add((S, Sp))
direct_flights.add((S, ST))
direct_flights.add((Sp, O))
direct_flights.add((Sp, ST))
direct_flights.add((Sp, S))
direct_flights.add((Sp, G))
direct_flights.add((G, O))
direct_flights.add((G, ST))
direct_flights.add((G, Sp))
direct_flights.add((G, P))
direct_flights.add((P, S))
direct_flights.add((P, O))
direct_flights.add((P, G))
direct_flights.add((T, R))
direct_flights.add((T, O))

# Add reverse flights for symmetry
for a, b in list(direct_flights):
    if (b, a) not in direct_flights:
        direct_flights.add((b, a))

# Create Z3 solver
s = Solver()

# Create the sequence of cities: seq[0] to seq[7]
seq = [Int(f'seq_{i}') for i in range(8)]

# Constraints:
# 1. seq[0] is R (0), seq[1] is ST (1)
s.add(seq[0] == R)
s.add(seq[1] == ST)

# 2. All cities are present exactly once
s.add(Distinct(seq))

# 3. For each consecutive pair, there is a direct flight
for i in range(7):
    a = seq[i]
    b = seq[i+1]
    s.add(Or([And(a == u, b == v) for u, v in direct_flights]))

# 4. Calculate start_day for each position and add constraint for P
start_day = [Int(f'start_day_{i}') for i in range(8)]
s.add(start_day[0] == 1)
for i in range(1, 8):
    prev_start = start_day[i-1]
    prev_duration = durations[seq[i-1]]
    s.add(start_day[i] == prev_start + prev_duration - 1)

# Constraint: there exists i such that seq[i] == P and start_day[i] == 19
for i in range(8):
    s.add(If(seq[i] == P, start_day[i] == 19, True))

# Now, solve the constraints
if s.check() == sat:
    m = s.model()
    sequence = [m.eval(seq[i]).as_long() for i in range(8)]
    city_names = {0: 'Reykjavik', 1: 'Stockholm', 2: 'Oslo', 3: 'Stuttgart', 4: 'Split', 5: 'Geneva', 6: 'Porto', 7: 'Tallinn'}
    day_to_city = {}
    for i in range(8):
        city = city_names[sequence[i]]
        s_i = m.eval(start_day[i]).as_long()
        d_i = durations[sequence[i]]
        for day in range(s_i, s_i + d_i):
            day_to_city[day] = city
    itinerary_list = []
    for day in sorted(day_to_city.keys()):
        itinerary_list.append({day: day_to_city[day]})
    print(json.dumps({'itinerary': itinerary_list}, indent=2))
else:
    print("No solution found.")