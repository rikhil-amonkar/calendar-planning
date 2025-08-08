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

# Define the direct flight set (as unordered pairs)
flight_set = {
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
}

# Create list of allowed ordered flight pairs (both directions)
allowed_ordered = []
for (c1, c2) in flight_set:
    allowed_ordered.append((c1, c2))
    allowed_ordered.append((c2, c1))

# Create Z3 variables for each day (days 1 to 17)
d = [Const(f'd_{i}', City) for i in range(1, 18)]  # d[0] is day1, d[16] is day17

s = Solver()

# Constraint: Each day must be one of the cities
for i in range(17):
    s.add(Or(
        d[i] == City.Brussels,
        d[i] == City.Rome,
        d[i] == City.Dubrovnik,
        d[i] == City.Geneva,
        d[i] == City.Budapest,
        d[i] == City.Riga,
        d[i] == City.Valencia
    ))

# Constraint: Consecutive days must either be the same city or connected by a direct flight
for i in range(16):
    same_city = d[i] == d[i+1]
    flight_connection = Or([And(d[i] == a, d[i+1] == b) for (a, b) in allowed_ordered])
    s.add(Or(same_city, flight_connection))

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

# Constraints for total days per city
for city, total in req_days.items():
    count1 = Sum([If(d[i] == city, 1, 0) for i in range(17)])
    count2 = Sum([If(And(d[i] == city, d[i+1] != city), 1, 0) for i in range(16)])
    s.add(count1 + count2 == total)

# Constraint: Brussels must have at least one day in [7, 11]
brussels_constraints = []
for day in [7, 8, 9, 10, 11]:
    idx = day - 1
    # Either in Brussels at the end of the day, or flew out of Brussels on this day
    cond = Or(
        d[idx] == City.Brussels,
        And(day > 1, d[idx-1] == City.Brussels, d[idx] != City.Brussels)
    )
    brussels_constraints.append(cond)
s.add(Or(brussels_constraints))

# Constraint: Budapest must have at least one day in [16, 17]
budapest_constraints = []
for day in [16, 17]:
    idx = day - 1
    if day == 17:
        # On day 17, only being in Budapest at the end counts (no flight out possible)
        cond = (d[idx] == City.Budapest)
    else:
        cond = Or(
            d[idx] == City.Budapest,
            And(day > 1, d[idx-1] == City.Budapest, d[idx] != City.Budapest)
        )
    budapest_constraints.append(cond)
s.add(Or(budapest_constraints))

# Constraint: Riga must have at least one day in [4, 7]
riga_constraints = []
for day in [4, 5, 6, 7]:
    idx = day - 1
    cond = Or(
        d[idx] == City.Riga,
        And(day > 1, d[idx-1] == City.Riga, d[idx] != City.Riga)
    )
    riga_constraints.append(cond)
s.add(Or(riga_constraints))

# Solve the problem
if s.check() == sat:
    model = s.model()
    itinerary = []
    for day in range(1, 18):
        city_val = model[d[day-1]]
        city_name = city_names[city_val]
        itinerary.append({"day": day, "city": city_name})
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")