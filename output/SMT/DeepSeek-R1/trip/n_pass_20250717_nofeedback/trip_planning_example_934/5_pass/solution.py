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

# Fixed constraint: Either s0 same as d[0] or direct flight exists (removed extra parenthesis)
s.add(Or(s0 == d[0], Or([And(s0 == a, d[0] == b) for (a, b) in allowed_ordered])))

# Constraint: Each day must be assigned to a valid city
for i in range(17):
    s.add(Or([d[i] == city for city in city_names.keys()]))

# Constraint: Consecutive days must be same city or connected by direct flight
for i in range(16):
    same_city = d[i] == d[i+1]
    flight_ok = Or([And(d[i] == a, d[i+1] == b) for (a, b) in allowed_ordered])
    s.add(Or(same_city, flight_ok))

# Required days per city (based on end-of-day assignment)
req_days = {
    City.Brussels: 5,
    City.Rome: 2,
    City.Dubrovnik: 3,
    City.Geneva: 5,
    City.Budapest: 2,
    City.Riga: 4,
    City.Valencia: 2
}

# Count days per city (only end-of-day assignments)
for city, total in req_days.items():
    count = Sum([If(d[i] == city, 1, 0) for i in range(17)])
    s.add(count == total)

# Time window constraints
# Brussels must have at least one day between 7-11 (days 7-11 = indices 6-10)
s.add(Or([d[i] == City.Brussels for i in [6,7,8,9,10]]))

# Budapest must have at least one day between 16-17 (days 16-17 = indices 15-16)
s.add(Or([d[i] == City.Budapest for i in [15,16]]))

# Riga must have at least one day between 4-7 (days 4-7 = indices 3-6)
s.add(Or([d[i] == City.Riga for i in [3,4,5,6]]))

# Solve and output
if s.check() == sat:
    model = s.model()
    # Evaluate all day assignments to concrete values
    days = [model.eval(d_i) for d_i in d]
    
    # Build itinerary by grouping consecutive days
    itinerary = []
    current_city = days[0]
    start_day = 1
    for day_idx in range(1, 17):
        if days[day_idx] != current_city:
            end_day = day_idx  # Last day of current segment
            itinerary.append({
                'day_range': f'Day {start_day}-{end_day}',
                'place': city_names[current_city]
            })
            current_city = days[day_idx]
            start_day = day_idx + 1
    # Add last segment
    itinerary.append({
        'day_range': f'Day {start_day}-17',
        'place': city_names[current_city]
    })
    
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print("No solution found")