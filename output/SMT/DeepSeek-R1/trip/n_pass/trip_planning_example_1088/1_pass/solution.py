from z3 import *

# City mapping
city_names = ["Reykjavik", "Oslo", "Stuttgart", "Split", "Geneva", "Porto", "Tallinn", "Stockholm"]
total_days = [2, 5, 5, 3, 2, 3, 5, 3]  # for cities in order

# Direct flights set (as tuples (min, max))
direct_flights_set = {
    (0, 1), (0, 2), (0, 6), (0, 7),
    (1, 3), (1, 4), (1, 5), (1, 6), (1, 7),
    (2, 3), (2, 5), (2, 7),
    (3, 4), (3, 7),
    (4, 5), (4, 7),
    (5, 1), (5, 2), (5, 4)  # Note: (5,1) is (1,5), etc. But we use min,max so we have (1,5) already.
}
# Remove duplicates by ensuring min < max and no self-loops
direct_flights_set_cleaned = set()
for a, b in direct_flights_set:
    if a == b:
        continue
    low = min(a, b)
    high = max(a, b)
    direct_flights_set_cleaned.add((low, high))
direct_flights_set = direct_flights_set_cleaned

# Create Z3 variables: c0 to c21
c = [Int(f'c{i}') for i in range(22)]

solver = Solver()

# Constraint: c0 = Reykjavik (0)
solver.add(c[0] == 0)

# Constraints: c[i] between 0 and 7
for i in range(1, 22):
    solver.add(c[i] >= 0, c[i] <= 7)

# Flight constraints for day1 to day21
for i in range(1, 22):
    flight_i = c[i-1] != c[i]
    # If flight, then the pair must be in direct_flights_set
    or_conditions = []
    for (a, b) in direct_flights_set:
        cond1 = And(c[i-1] == a, c[i] == b)
        cond2 = And(c[i-1] == b, c[i] == a)
        or_conditions.append(Or(cond1, cond2))
    solver.add(Implies(flight_i, Or(or_conditions)))

# Total days constraints for each city
for x in range(8):
    conditions = []
    # Day 1: 
    #   present if: x==c0 or (flight1 and x==c1)
    flight1 = (c[0] != c[1])
    cond_day1 = Or(x == c[0], And(flight1, x == c[1]))
    conditions.append(cond_day1)
    # Days 2 to 21: present if: x == c[i-1] or (flight_i and x == c[i])
    for day_index in range(2, 22):  # day_index: 2 to 21
        # For day_index, we use c[day_index-1] (which is the city at the end of the previous day) and c[day_index] (city at the end of this day)
        flight_day = (c[day_index-1] != c[day_index])
        cond = Or(x == c[day_index-1], And(flight_day, x == c[day_index]))
        conditions.append(cond)
    # Now, the total days for city x is the sum of the conditions (each condition is a boolean that counts as 1 if true)
    total_here = Sum([If(cond, 1, 0) for cond in conditions])
    solver.add(total_here == total_days[x])

# Fixed event: Reykjavik (0) must be present on day2 (which is the second day, index1 in conditions list: conditions[1] is day2)
# conditions[0] is day1, conditions[1] is day2, ... conditions[20] is day21.
# We can use the conditions list we built for the total days. But note: we have to extract the condition for day2 for city0.
# Alternatively, rebuild for city0 day2:
flight2 = (c[1] != c[2])
cond_day2 = Or(0 == c[1], And(flight2, 0 == c[2]))
solver.add(cond_day2)

# Porto (5) must be present on day19,20,21
# Day19: day index 18 in our conditions list? 
# Our conditions list for city5: 
#   We need to extract the condition for day19: which is the 18th condition (since day1:0, day2:1, ... day19:18)
# But we can recompute for each day for city5:
cond_day19 = Or(5 == c[18], And(c[18] != c[19], 5 == c[19]))
cond_day20 = Or(5 == c[19], And(c[19] != c[20], 5 == c[20]))
cond_day21 = Or(5 == c[20], And(c[20] != c[21], 5 == c[21]))
solver.add(cond_day19)
solver.add(cond_day20)
solver.add(cond_day21)

# Stockholm (7) must be present on at least one of day2,3,4
cond_day2_stock = Or(7 == c[1], And(c[1] != c[2], 7 == c[2]))
cond_day3_stock = Or(7 == c[2], And(c[2] != c[3], 7 == c[3]))
cond_day4_stock = Or(7 == c[3], And(c[3] != c[4], 7 == c[4]))
solver.add(Or(cond_day2_stock, cond_day3_stock, cond_day4_stock))

# Solve
if solver.check() == sat:
    model = solver.model()
    c_vals = [model.evaluate(c[i]).as_long() for i in range(22)]
    
    # Build present_days: for each city, the set of days it is present
    present_days = [set() for _ in range(8)]
    # For day1:
    day1 = 1
    c0_val = c_vals[0]
    c1_val = c_vals[1]
    present_days[c0_val].add(day1)
    if c0_val != c1_val:
        present_days[c1_val].add(day1)
    # For days 2 to 21:
    for day in range(2, 22):  # day from 2 to 21
        # the city at the beginning: c[day-1] (which is c_vals[day-1])
        # and if flight, then also c_vals[day]
        c_prev = c_vals[day-1]
        c_curr = c_vals[day]
        present_days[c_prev].add(day)
        if c_prev != c_curr:
            present_days[c_curr].add(day)
    
    # Now, for each city, find continuous intervals in present_days
    itinerary = []
    for city in range(8):
        days = sorted(present_days[city])
        if not days:
            continue
        intervals = []
        start = days[0]
        end = days[0]
        for d in days[1:]:
            if d == end + 1:
                end = d
            else:
                intervals.append((start, end))
                start = d
                end = d
        intervals.append((start, end))
        for (s, e) in intervals:
            if s == e:
                itinerary.append({"day_range": f"Day {s}", "place": city_names[city]})
            else:
                itinerary.append({"day_range": f"Day {s}-{e}", "place": city_names[city]})
    
    # Now, add flight day records: for each flight day i (from 1 to 21) if c[i-1] != c[i]
    for day in range(1, 22):
        if c_vals[day-1] != c_vals[day]:
            city_dep = city_names[c_vals[day-1]]
            city_arr = city_names[c_vals[day]]
            itinerary.append({"day_range": f"Day {day}", "place": city_dep})
            itinerary.append({"day_range": f"Day {day}", "place": city_arr})
    
    # We need to sort the itinerary by the first day of the range? 
    # But the problem does not specify order. We can try to sort by the day_range.
    # However, the example output is in the order of the trip.
    # How to sort? 
    #   We can extract the start day from the day_range string.
    def get_start_day(entry):
        s = entry['day_range']
        if s.startswith('Day '):
            parts = s[4:].split('-')
            return int(parts[0])
        return 0
    
    itinerary_sorted = sorted(itinerary, key=get_start_day)
    
    # Output as JSON
    import json
    result = {"itinerary": itinerary_sorted}
    print(json.dumps(result))
else:
    print("No solution found")