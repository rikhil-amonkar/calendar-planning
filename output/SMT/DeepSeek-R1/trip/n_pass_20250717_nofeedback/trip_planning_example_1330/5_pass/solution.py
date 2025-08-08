from z3 import *

# Define cities and flight connections
cities = ['Salzburg', 'Hamburg', 'Venice', 'Nice', 'Zurich', 'Bucharest', 'Copenhagen', 'Brussels', 'Naples', 'Barcelona']
City, city_consts = EnumSort('City', cities)
salzburg, hamburg, venice, nice, zurich, bucharest, copenhagen, brussels, naples, barcelona = city_consts

direct_flights = [
    (salzburg, hamburg), (salzburg, venice), (salzburg, nice), (salzburg, zurich),
    (hamburg, salzburg), (hamburg, venice), (hamburg, nice), (hamburg, zurich), (hamburg, bucharest), 
    (hamburg, copenhagen), (hamburg, brussels), (hamburg, naples), (hamburg, barcelona),
    (venice, salzburg), (venice, hamburg), (venice, nice), (venice, zurich), (venice, bucharest), 
    (venice, naples), (venice, barcelona),
    (nice, salzburg), (nice, hamburg), (nice, venice), (nice, zurich), (nice, brussels), (nice, barcelona),
    (zurich, salzburg), (zurich, hamburg), (zurich, venice), (zurich, nice), (zurich, bucharest), 
    (zurich, copenhagen), (zurich, brussels), (zurich, naples), (zurich, barcelona),
    (bucharest, hamburg), (bucharest, venice), (bucharest, zurich), (bucharest, copenhagen), 
    (bucharest, brussels), (bucharest, naples), (bucharest, barcelona),
    (copenhagen, hamburg), (copenhagen, zurich), (copenhagen, bucharest), (copenhagen, brussels), 
    (copenhagen, naples), (copenhagen, barcelona),
    (brussels, hamburg), (brussels, nice), (brussels, zurich), (brussels, bucharest), 
    (brussels, copenhagen), (brussels, naples), (brussels, barcelona),
    (naples, hamburg), (naples, venice), (naples, zurich), (naples, bucharest), 
    (naples, copenhagen), (naples, brussels), (naples, barcelona),
    (barcelona, hamburg), (barcelona, venice), (barcelona, nice), (barcelona, zurich), 
    (barcelona, bucharest), (barcelona, copenhagen), (barcelona, brussels), (barcelona, naples)
]

s = Solver()

# City for each day (0-24 for days 1-25)
city_day = [Const(f'city_{i}', City) for i in range(25)]

# Each day is one city
for i in range(25):
    s.add(Or([city_day[i] == c for c in city_consts]))

# Start and end constraints
s.add(city_day[0] == salzburg)
s.add(city_day[24] == naples)

# Flight constraints between consecutive days
for i in range(24):
    current = city_day[i]
    next_day = city_day[i+1]
    s.add(Or(
        current == next_day,  # Stay in same city
        Or([And(current == src, next_day == dst) for (src, dst) in direct_flights])  # Or take direct flight
    ))

# Each city must appear at least once
for c in city_consts:
    s.add(Or([city_day[i] == c for i in range(25)]))

# Define start and end days for each city
city_starts = [Int(f'start_{c}') for c in cities]
city_ends = [Int(f'end_{c}') for c in cities]

# Interval constraints for contiguous blocks
for idx, c in enumerate(city_consts):
    start_var = city_starts[idx]
    end_var = city_ends[idx]
    
    # Start and end between 1-25, start <= end
    s.add(start_var >= 1, start_var <= 25)
    s.add(end_var >= 1, end_var <= 25)
    s.add(start_var <= end_var)
    
    # City appears on day i iff i is between start and end (inclusive)
    for i in range(25):
        day_num = i + 1
        s.add((city_day[i] == c) == And(start_var <= day_num, day_num <= end_var))

# Ensure intervals cover entire period without gaps/overlaps
# 1. All intervals are disjoint (no overlap)
for i in range(len(cities)):
    for j in range(i+1, len(cities)):
        s.add(Or(
            city_ends[i] < city_starts[j],  # i ends before j starts
            city_ends[j] < city_starts[i]   # j ends before i starts
        ))
        
# 2. Intervals cover all days 1-25
covered = []
for day in range(1, 26):
    day_covered = Or([
        And(city_starts[i] <= day, day <= city_ends[i]) 
        for i in range(len(cities))
    ])
    covered.append(day_covered)
s.add(And(covered))

# 3. Intervals are contiguous (no gaps between blocks)
for i in range(len(cities)):
    for j in range(len(cities)):
        if i == j:
            continue
        # If city j starts right after city i ends
        adjacent = And(city_ends[i] + 1 == city_starts[j])
        # There must be no other city between them
        no_city_between = True
        for k in range(len(cities)):
            if k == i or k == j:
                continue
            no_city_between = And(no_city_between, 
                Or(city_ends[k] < city_ends[i], city_starts[k] > city_starts[j]))
        # Enforce ordering if adjacent
        s.add(Implies(adjacent, no_city_between))

# Solve and output itinerary
if s.check() == sat:
    m = s.model()
    # Build chronological itinerary
    itinerary = []
    current_city = str(m.evaluate(city_day[0]))
    start_day = 1
    for i in range(1, 25):
        city_str = str(m.evaluate(city_day[i]))
        if city_str != current_city:
            itinerary.append({'day_range': f'Day {start_day}-{i}', 'place': current_city})
            current_city = city_str
            start_day = i+1
    itinerary.append({'day_range': f'Day {start_day}-25', 'place': current_city})
    
    print(f"Plan found: {{'itinerary': {itinerary}}}")
else:
    print("No valid plan found.")