from z3 import *

# Define city names and their integer mappings
city_names = ["Bucharest", "Warsaw", "Stuttgart", "Copenhagen", "Dubrovnik"]
city_map = {name: idx for idx, name in enumerate(city_names)}

# Direct flights as tuples of city indices
direct_flights_list = [
    (city_map["Warsaw"], city_map["Copenhagen"]),
    (city_map["Stuttgart"], city_map["Copenhagen"]),
    (city_map["Warsaw"], city_map["Stuttgart"]),
    (city_map["Bucharest"], city_map["Copenhagen"]),
    (city_map["Bucharest"], city_map["Warsaw"]),
    (city_map["Copenhagen"], city_map["Dubrovnik"])
]

# Create Z3 variables for days 1 to 19
days = list(range(1, 20))
L = [Int('L_%d' % d) for d in days]
Fly = [Bool('Fly_%d' % d) for d in days]
Dest = [Int('Dest_%d' % d) for d in days]

solver = Solver()

# Constraints for L: each L[d] must be between 0 and 4 (inclusive)
for d in days:
    solver.add(L[d-1] >= 0, L[d-1] <= 4)
    solver.add(Dest[d-1] >= 0, Dest[d-1] <= 4)

# Flight validity constraint: if Fly[d] is True, then (L[d], Dest[d]) must be in direct_flights_list (in any order)
for d in days:
    idx = d-1
    flight_cond = Or([Or(And(L[idx] == c1, Dest[idx] == c2), And(L[idx] == c2, Dest[idx] == c1)) for (c1, c2) in direct_flights_list])
    solver.add(Implies(Fly[idx], flight_cond))
    # Also, if flying, L[d] != Dest[d]
    solver.add(Implies(Fly[idx], L[idx] != Dest[idx]))

# Next day constraints for L: for d from 1 to 18
for d in days[:-1]:  # days 1 to 18
    idx = d-1
    solver.add(If(Fly[idx], L[idx+1] == Dest[idx], L[idx+1] == L[idx]))

# Constraints for total days in each city
# We'll define in_city[d][c] as a boolean expression
in_city_expr = {}
for d in days:
    idx = d-1
    for c in range(5):
        in_city_expr[(d, c)] = Or(
            And(Not(Fly[idx]), L[idx] == c),
            And(Fly[idx], Or(L[idx] == c, Dest[idx] == c))
        )

# Total days per city
total_days = [0]*5
for c in range(5):
    total_days[c] = Sum([If(in_city_expr[(d, c)], 1, 0) for d in days])
solver.add(total_days[city_map["Bucharest"]] == 6)
solver.add(total_days[city_map["Warsaw"]] == 2)
solver.add(total_days[city_map["Stuttgart"]] == 7)
solver.add(total_days[city_map["Copenhagen"]] == 3)
solver.add(total_days[city_map["Dubrovnik"]] == 5)

# Specific day constraints: Stuttgart on day 7 and 13
solver.add(in_city_expr[(7, city_map["Stuttgart"])] == True)
solver.add(in_city_expr[(13, city_map["Stuttgart"])] == True)

# Bucharest wedding: must be in Bucharest on at least one day between 1 and 6
solver.add(Or([in_city_expr[(d, city_map["Bucharest"])] for d in range(1, 7)]))

# Total flights must be 4
total_flights = Sum([If(Fly[d-1], 1, 0) for d in days])
solver.add(total_flights == 4)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    # Evaluate L, Fly, Dest for each day
    L_val = [model.evaluate(L[i]).as_long() for i in range(19)]
    Fly_val = [model.evaluate(Fly[i]) for i in range(19)]
    Dest_val = [model.evaluate(Dest[i]).as_long() for i in range(19)]
    
    # Build the set of days for each city
    in_city_days = {c: set() for c in range(5)}
    for d in days:
        idx = d-1
        if Fly_val[idx]:
            in_city_days[L_val[idx]].add(d)
            in_city_days[Dest_val[idx]].add(d)
        else:
            in_city_days[L_val[idx]].add(d)
    
    # Find contiguous intervals for each city
    blocks = []
    for c in range(5):
        if not in_city_days[c]:
            continue
        sorted_days = sorted(in_city_days[c])
        start = sorted_days[0]
        end = start
        for i in range(1, len(sorted_days)):
            if sorted_days[i] == end + 1:
                end = sorted_days[i]
            else:
                blocks.append((start, end, c))
                start = sorted_days[i]
                end = start
        blocks.append((start, end, c))
    
    # Create records: blocks and flight records
    records = []
    # Block records
    for (s, e, c) in blocks:
        if s == e:
            day_range_str = "Day %d" % s
        else:
            day_range_str = "Day %d-%d" % (s, e)
        place = city_names[c]
        key = (s, 1)  # 1 for block
        records.append((key, {"day_range": day_range_str, "place": place}))
    
    # Flight records: for each flight day, two records
    for d in days:
        idx = d-1
        if is_true(Fly_val[idx]):
            # Departure city
            c1 = L_val[idx]
            record1 = {"day_range": "Day %d" % d, "place": city_names[c1]}
            key1 = (d, 0)  # 0 for flight record
            records.append((key1, record1))
            # Arrival city
            c2 = Dest_val[idx]
            record2 = {"day_range": "Day %d" % d, "place": city_names[c2]}
            key2 = (d, 0)
            records.append((key2, record2))
    
    # Sort records: by key = (start_day, type) where type: 0 (flight) comes before 1 (block)
    records_sorted = sorted(records, key=lambda x: (x[0][0], x[0][1]))
    itinerary = [rec for (key, rec) in records_sorted]
    
    # Output as JSON
    output = {"itinerary": itinerary}
    print(output)
else:
    print("No solution found")