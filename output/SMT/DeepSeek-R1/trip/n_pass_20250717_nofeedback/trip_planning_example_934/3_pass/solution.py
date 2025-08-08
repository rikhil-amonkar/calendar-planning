from z3 import *
import json

# Define the city enumeration
City = Datatype('City')
City.declare('Brussels')
City.declare('Rome')
City.declare('Dubrovnik')
City.declare('Geneva')
City.declare('Budapest')
City.declare('Riga')
City.declare('Valencia')
City = City.create()

# City names for output
city_names = {
    City.Brussels: "Brussels",
    City.Rome: "Rome",
    City.Dubrovnik: "Dubrovnik",
    City.Geneva: "Geneva",
    City.Budapest: "Budapest",
    City.Riga: "Riga",
    City.Valencia: "Valencia"
}

# Define direct flight connections (unordered pairs)
flight_pairs = [
    (City.Brussels, City.Valencia),
    (City.Rome, City.Valencia),
    (City.Brussels, City.Geneva),
    (City.Rome, City.Geneva),
    (City.Dubrovnik, City.Geneva),
    (City.Valencia, City.Geneva),
    (City.Rome, City.Riga),
    (City.Geneva, City.Budapest),
    (City.Riga, City.Brussels),
    (City.Rome, City.Budapest),
    (City.Rome, City.Brussels),
    (City.Brussels, City.Budapest),
    (City.Dubrovnik, City.Rome)
]

# Create list of allowed ordered flight pairs (both directions)
allowed_ordered = []
for (c1, c2) in flight_pairs:
    allowed_ordered.append((c1, c2))
    allowed_ordered.append((c2, c1))

# Create Z3 variables for each day (days 1 to 17)
d = [Const(f'd_{i}', City) for i in range(17)]  # d[0] is day1, d[16] is day17
s0 = Const('s0', City)  # Start city before day1

s = Solver()

# Constraint: s0 must be one of the cities
s.add(Or([s0 == city for city in city_names.keys()]))

# Constraint: Either s0 same as d[0] or direct flight exists
s.add(Or(s0 == d[0], Or([And(s0 == a, d[0] == b) for (a, b) in allowed_ordered])))

# Constraint: Each day must be assigned to a valid city
for i in range(17):
    s.add(Or([d[i] == city for city in city_names.keys()]))

# Constraint: Consecutive days must be same city or connected by direct flight
for i in range(16):
    same_city = d[i] == d[i+1]
    flight_ok = Or([And(d[i] == a, d[i+1] == b) for (a, b) in allowed_ordered])
    s.add(Or(same_city, flight_ok))

# Required days per city
req_days = {
    City.Brussels: 5,
    City.Rome: 2,
    City.Dubrovnik: 3,
    City.Geneva: 5,
    City.Budapest: 2,
    City.Riga: 4,
    City.Valencia: 2
}

# New constraint: Count days in each city (including flight days)
for city, total in req_days.items():
    count = 0
    # Day 1: s0 and d[0]
    count += If(Or(s0 == city, d[0] == city), 1, 0)
    # Days 2-17: d[i-1] and d[i] for i in 1..16
    for i in range(16):
        count += If(Or(d[i] == city, d[i+1] == city), 1, 0)
    s.add(count == total)

# Time window constraints
# Brussels must have at least one day between 7-11
brussels_days = []
for day in [7, 8, 9, 10, 11]:
    if day == 1:
        cond = Or(s0 == City.Brussels, d[0] == City.Brussels)
    else:
        cond = Or(d[day-2] == City.Brussels, d[day-1] == City.Brussels)
    brussels_days.append(cond)
s.add(Or(brussels_days))

# Budapest must have at least one day between 16-17
budapest_days = []
for day in [16, 17]:
    if day == 1:
        cond = Or(s0 == City.Budapest, d[0] == City.Budapest)
    else:
        cond = Or(d[day-2] == City.Budapest, d[day-1] == City.Budapest)
    budapest_days.append(cond)
s.add(Or(budapest_days))

# Riga must have at least one day between 4-7
riga_days = []
for day in [4, 5, 6, 7]:
    if day == 1:
        cond = Or(s0 == City.Riga, d[0] == City.Riga)
    else:
        cond = Or(d[day-2] == City.Riga, d[day-1] == City.Riga)
    riga_days.append(cond)
s.add(Or(riga_days))

# Solve and output
if s.check() == sat:
    model = s.model()
    # Build itinerary by grouping consecutive days
    itinerary = []
    current_city = model[d[0]]
    start_day = 1
    for day_idx in range(1, 17):
        if model[d[day_idx]] != current_city:
            end_day = day_idx
            itinerary.append({
                'day_range': f'Day {start_day}-{end_day}',
                'place': city_names[current_city]
            })
            current_city = model[d[day_idx]]
            start_day = day_idx + 1
    # Add last segment
    itinerary.append({
        'day_range': f'Day {start_day}-17',
        'place': city_names[current_city]
    })
    
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print("No solution found")