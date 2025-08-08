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
d = [Const(f'd_{i}', City) for i in range(17)]  # d[0] is day1, d[16] is day17

# Create the start city variable
s0 = Const('s0', City)

s = Solver()

# Constraint: s0 must be one of the cities
s.add(Or(
    s0 == City.Brussels,
    s0 == City.Rome,
    s0 == City.Dubrovnik,
    s0 == City.Geneva,
    s0 == City.Budapest,
    s0 == City.Riga,
    s0 == City.Valencia
))

# Constraint: Either the start city is the same as the end of day1, or there is a direct flight
first_flight_constraints = [s0 == d[0]]  # staying in the same city
for (a, b) in allowed_ordered:
    first_flight_constraints.append(And(s0 == a, d[0] == b))
s.add(Or(first_flight_constraints))

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
for i in range(16):  # from day1 to day16 (d[0] to d[15]) and next day (d[1] to d[16])
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
    count2 = Sum([If(And(d[i] == city, i < 16, d[i+1] != city), 1, 0) for i in range(16)])
    count3 = If(And(s0 == city, d[0] != city), 1, 0)
    s.add(count1 + count2 + count3 == total)

# Constraint: Brussels must have at least one day in [7, 11]
brussels_constraints = []
for day in [7, 8, 9, 10, 11]:
    idx = day - 1  # day7 -> d[6], day11 -> d[10]
    if day == 1:
        cond = Or(d[0] == City.Brussels, 
                 And(s0 == City.Brussels, d[0] != City.Brussels))
    else:
        cond = Or(d[idx] == City.Brussels,
                 And(d[idx-1] == City.Brussels, d[idx] != City.Brussels))
    brussels_constraints.append(cond)
s.add(Or(brussels_constraints))

# Constraint: Budapest must have at least one day in [16, 17]
budapest_constraints = []
for day in [16, 17]:
    idx = day - 1  # day16 -> d[15], day17 -> d[16]
    if day == 1:
        cond = Or(d[0] == City.Budapest,
                 And(s0 == City.Budapest, d[0] != City.Budapest))
    else:
        if day == 17:
            cond = Or(d[16] == City.Budapest,
                     And(d[15] == City.Budapest, d[16] != City.Budapest))
        else:
            cond = Or(d[idx] == City.Budapest,
                     And(d[idx-1] == City.Budapest, d[idx] != City.Budapest))
    budapest_constraints.append(cond)
s.add(Or(budapest_constraints))

# Constraint: Riga must have at least one day in [4, 7]
riga_constraints = []
for day in [4, 5, 6, 7]:
    idx = day - 1  # day4 -> d[3], day7 -> d[6]
    if day == 1:
        cond = Or(d[0] == City.Riga,
                 And(s0 == City.Riga, d[0] != City.Riga))
    else:
        cond = Or(d[idx] == City.Riga,
                 And(d[idx-1] == City.Riga, d[idx] != City.Riga))
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