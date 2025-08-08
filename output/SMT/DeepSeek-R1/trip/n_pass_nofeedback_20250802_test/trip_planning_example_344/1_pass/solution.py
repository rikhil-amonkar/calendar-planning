from z3 import *
import json

# Define the City datatype
City = Datatype('City')
City.declare('Athens')
City.declare('Valencia')
City.declare('Naples')
City.declare('Zurich')
City = City.create()

# Define direct flights as a list of tuples (from_city, to_city)
direct_flights = [
    (City.Athens, City.Valencia),
    (City.Valencia, City.Athens),
    (City.Valencia, City.Naples),
    (City.Naples, City.Valencia),
    (City.Valencia, City.Zurich),
    (City.Zurich, City.Valencia),
    (City.Athens, City.Naples),
    (City.Naples, City.Athens),
    (City.Athens, City.Zurich),
    (City.Zurich, City.Athens),
    (City.Zurich, City.Naples),
    (City.Naples, City.Zurich)
]

# Create a solver
s = Solver()

# Define variables for the middle cities
c1 = Const('c1', City)
c2 = Const('c2', City)

# Constraints: c1 and c2 must be Zurich or Valencia and not the same
s.add(Or(c1 == City.Zurich, c1 == City.Valencia))
s.add(Or(c2 == City.Zurich, c2 == City.Valencia))
s.add(c1 != c2)

# Helper function to check direct flights
def is_direct(from_city, to_city):
    return Or([And(from_city == f[0], to_city == f[1]) for f in direct_flights])

# Flight constraints
s.add(is_direct(City.Athens, c1))      # Flight from Athens to c1 on day 6
s.add(is_direct(c1, c2))               # Flight from c1 to c2 on day 11
s.add(is_direct(c2, City.Naples))      # Flight from c2 to Naples on day 16

# Solve the model
if s.check() == sat:
    m = s.model()
    c1_val = m[c1]
    c2_val = m[c2]
    c1_str = c1_val.decl().name()
    c2_str = c2_val.decl().name()
    
    # Build itinerary
    itinerary = []
    
    # Days 1-5: Athens
    for day in range(1, 6):
        itinerary.append({"day": day, "city": ["Athens"]})
    
    # Day 6: Athens and c1
    itinerary.append({"day": 6, "city": ["Athens", c1_str]})
    
    # Days 7-10: c1
    for day in range(7, 11):
        itinerary.append({"day": day, "city": [c1_str]})
    
    # Day 11: c1 and c2
    itinerary.append({"day": 11, "city": [c1_str, c2_str]})
    
    # Days 12-15: c2
    for day in range(12, 16):
        itinerary.append({"day": day, "city": [c2_str]})
    
    # Day 16: c2 and Naples
    itinerary.append({"day": 16, "city": [c2_str, "Naples"]})
    
    # Days 17-20: Naples
    for day in range(17, 21):
        itinerary.append({"day": day, "city": ["Naples"]})
    
    # Create result dictionary
    result = {"itinerary": itinerary}
    
    # Output as JSON
    print(json.dumps(result, indent=2))
else:
    print("No solution found")