from z3 import *
import json

# Cities encoding
dublin = 0
krakow = 1
istanbul = 2
venice = 3
naples = 4
brussels = 5
mykonos = 6
frankfurt = 7

city_names = {
    0: "Dublin",
    1: "Krakow",
    2: "Istanbul",
    3: "Venice",
    4: "Naples",
    5: "Brussels",
    6: "Mykonos",
    7: "Frankfurt"
}

# Required days per city
days_arr = [5, 4, 3, 3, 4, 2, 4, 3]  # index 0 to 7

# Flight edges: normalized as (min, max)
raw_edges = [
    (0,5), (6,4), (3,2), (7,1), (4,0), (1,5), (4,2), (4,5), (2,7), (5,7), (2,1), (2,5), (3,7), (4,7), (0,1), (3,5), (4,3), (2,0), (3,0), (0,7)
]
edges = set()
for (u, v) in raw_edges:
    a, b = min(u, v), max(u, v)
    edges.add((a, b))
edges = list(edges)

# Create the solver
s = Solver()

# Define the sequence: 8 integers
seq = IntVector('seq', 8)

# Each element between 0 and 7
for i in range(8):
    s.add(seq[i] >= 0)
    s.add(seq[i] <= 7)

# Distinct sequence
s.add(Distinct(seq))

# Define the cumulative sums: 9 elements, cum_sum[0] to cum_sum[8]
cum_sum = IntVector('cum_sum', 9)
s.add(cum_sum[0] == 0)

# Define an array for the days of the sequence elements
seq_days = [Int(f'seq_days_{i}') for i in range(8)]
for i in range(8):
    # Build a chain of If conditions to assign days_arr based on seq[i]
    cases = []
    for city in range(8):
        cases.append((city, days_arr[city]))
    expr = If(seq[i] == 7, cases[7][1],
           If(seq[i] == 6, cases[6][1],
           If(seq[i] == 5, cases[5][1],
           If(seq[i] == 4, cases[4][1],
           If(seq[i] == 3, cases[3][1],
           If(seq[i] == 2, cases[2][1],
           If(seq[i] == 1, cases[1][1],
           If(seq[i] == 0, cases[0][1], 0))))))))
    s.add(seq_days[i] == expr)

# Define the cumulative sums
for i in range(1, 9):
    s.add(cum_sum[i] == cum_sum[i-1] + seq_days[i-1])

# Constraints for specific cities
# Dublin: must start at day 11
dub_constraint = Or([And(seq[i] == dublin, (1 + cum_sum[i] - i) == 11) for i in range(8)])
s.add(dub_constraint)

# Mykonos: start day <= 4
myk_constraint = Or([And(seq[i] == mykonos, (1 + cum_sum[i] - i) <= 4) for i in range(8)])
s.add(myk_constraint)

# Istanbul: 7 <= start day <= 11
ist_constraint = Or([And(seq[i] == istanbul, 
                        And((1 + cum_sum[i] - i) >= 7, 
                            (1 + cum_sum[i] - i) <= 11)) for i in range(8)])
s.add(ist_constraint)

# Frankfurt: 13 <= start day <= 17
fra_constraint = Or([And(seq[i] == frankfurt, 
                         And((1 + cum_sum[i] - i) >= 13, 
                             (1 + cum_sum[i] - i) <= 17)) for i in range(8)])
s.add(fra_constraint)

# Flight constraints for consecutive cities
for i in range(7):
    u = seq[i]
    v = seq[i+1]
    cond = False
    for (a, b) in edges:
        cond = Or(cond, Or(And(u == a, v == b), And(u == b, v == a)))
    s.add(cond)

# Total days must be 28
s.add(cum_sum[8] == 28)

# Solve the problem
if s.check() == sat:
    m = s.model()
    seq_val = [m.evaluate(seq[i]).as_long() for i in range(8)]
    
    # Compute cumulative sums and start/end days
    cum_sum_val = [0]
    for i in range(8):
        c = seq_val[i]
        d = days_arr[c]
        cum_sum_val.append(cum_sum_val[-1] + d)
    
    start_days = [1 + cum_sum_val[i] - i for i in range(8)]
    end_days = [start_days[i] + days_arr[seq_val[i]] - 1 for i in range(8)]
    
    # Build itinerary
    itinerary = []
    for day in range(1, 22):
        cities_today = []
        for i in range(8):
            if start_days[i] <= day <= end_days[i]:
                cities_today.append(city_names[seq_val[i]])
        if len(cities_today) == 1:
            city_entry = cities_today[0]
        else:
            city_entry = cities_today
        itinerary.append({"day": day, "city": city_entry})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print("No solution found")