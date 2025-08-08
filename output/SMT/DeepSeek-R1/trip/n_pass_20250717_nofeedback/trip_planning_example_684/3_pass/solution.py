from z3 import *

# Define the Place datatype
Place = Datatype('Place')
Place.declare('EDI')
Place.declare('LHR')
Place.declare('JFK')
Place.declare('NCE')
Place = Place.create()

# Function to return flight time between two places
def flight_time_expr(p1, p2):
    cond_EDI_LHR = Or(And(p1 == Place.EDI, p2 == Place.LHR), And(p1 == Place.LHR, p2 == Place.EDI))
    cond_EDI_JFK = Or(And(p1 == Place.EDI, p2 == Place.JFK), And(p1 == Place.JFK, p2 == Place.EDI))
    cond_EDI_NCE = Or(And(p1 == Place.EDI, p2 == Place.NCE), And(p1 == Place.NCE, p2 == Place.EDI))
    cond_LHR_JFK = Or(And(p1 == Place.LHR, p2 == Place.JFK), And(p1 == Place.JFK, p2 == Place.LHR))
    cond_LHR_NCE = Or(And(p1 == Place.LHR, p2 == Place.NCE), And(p1 == Place.NCE, p2 == Place.LHR))
    cond_JFK_NCE = Or(And(p1 == Place.JFK, p2 == Place.NCE), And(p1 == Place.NCE, p2 == Place.JFK))
    
    return If(cond_EDI_LHR, 60,
           If(cond_EDI_JFK, 360,
           If(cond_EDI_NCE, 120,
           If(cond_LHR_JFK, 420,
           If(cond_LHR_NCE, 120,
           If(cond_JFK_NCE, 480, 0))))))

# Create solver
s = Solver()

# Sequence variables
s0, s1, s2, s3 = Consts('s0 s1 s2 s3', Place)

# Arrival and departure functions
base_arr = Function('base_arr', Place, IntSort())
base_dep = Function('base_dep', Place, IntSort())

# Constraints
constraints = []

# All airports are distinct
constraints.append(Distinct(s0, s1, s2, s3))

# Bounds and turnaround times for each airport
airports = [Place.EDI, Place.LHR, Place.JFK, Place.NCE]
for airport in airports:
    constraints.append(base_arr(airport) >= 0)
    constraints.append(base_arr(airport) <= 1440)
    constraints.append(base_dep(airport) >= 0)
    constraints.append(base_dep(airport) <= 1440)
    constraints.append(base_dep(airport) >= base_arr(airport) + 30)

# Sequence constraints
constraints.append(base_arr(s1) == base_dep(s0) + flight_time_expr(s0, s1))
constraints.append(base_arr(s2) == base_dep(s1) + flight_time_expr(s1, s2))
constraints.append(base_arr(s3) == base_dep(s2) + flight_time_expr(s2, s3))

# EDI must be before LHR in the sequence
index_EDI = If(s0 == Place.EDI, 0, 
              If(s1 == Place.EDI, 1, 
               If(s2 == Place.EDI, 2, 3)))
index_LHR = If(s0 == Place.LHR, 0, 
              If(s1 == Place.LHR, 1, 
               If(s2 == Place.LHR, 2, 3)))
constraints.append(index_EDI < index_LHR)

# Add all constraints to the solver
s.add(constraints)

# Minimize base_arr[LHR]
objective = base_arr(Place.LHR)
min_obj = 1441  # Start with a value larger than max possible (1440)
model = None

while s.check() == sat:
    m = s.model()
    current_obj = m.eval(objective).as_long()
    if current_obj < min_obj:
        min_obj = current_obj
        model = m
    s.add(objective < current_obj)

# Output the result
if model is not None:
    print(f"Minimum base_arr[LHR]: {min_obj}")
else:
    print("No solution found")