from z3 import Solver, Int, Distinct, If, And, Or, sat
import json

# Initialize the solver
s = Solver()

# Define the end days for the stays
E2 = Int('E2')
E3 = Int('E3')
E4 = Int('E4')

# Define the city variables for the stays (2nd to 5th)
c2 = Int('c2')
c3 = Int('c3')
c4 = Int('c4')
c5 = Int('c5')

# Cities mapping: 1=Paris, 2=Oslo, 3=Porto, 4=Reykjavik

# Constraints for the end days
s.add(E2 >= 8, E2 <= 23)
s.add(E3 >= E2, E3 <= 23)
s.add(E4 >= E3, E4 <= 23)

# Cities must be distinct and in {1,2,3,4}
s.add(Distinct(c2, c3, c4, c5))
s.add(c2 >= 1, c2 <= 4)
s.add(c3 >= 1, c3 <= 4)
s.add(c4 >= 1, c4 <= 4)
s.add(c5 >= 1, c5 <= 4)

# Stay2: from day7 to E2, length = E2 - 6
s.add(E2 == If(c2 == 1, 12, If(c2 == 2, 11, If(c2 == 3, 13, 8))))  # 8 for c2=4 (Reykjavik)

# Stay3: from E2 to E3, length = E3 - E2 + 1
s.add(E3 == If(c3 == 1, E2 + 5, 
               If(c3 == 2, E2 + 4,
                  If(c3 == 3, E2 + 6, 
                     E2 + 1))))  # +1 for c3=4

# Stay4: from E3 to E4, length = E4 - E3 + 1
s.add(E4 == If(c4 == 1, E3 + 5, 
               If(c4 == 2, E3 + 4,
                  If(c4 == 3, E3 + 6, 
                     E3 + 1))))  # +1 for c4=4

# Stay5: from E4 to 23, length = 24 - E4
s.add(Or(
    And(c5 == 1, E4 == 18),
    And(c5 == 2, E4 == 19),
    And(c5 == 3, E4 == 17),
    And(c5 == 4, E4 == 22)
))

# Connectivity constraints: first travel from Geneva (0) to c2 must be allowed (c2 in {1,2,3})
s.add(Or(c2 == 1, c2 == 2, c2 == 3))

# Function to check direct flight connectivity between two cities (excluding Geneva in the next stays)
def edge(i, j):
    return Or(
        And(i == 1, Or(j == 2, j == 3, j == 4)),
        And(i == 2, Or(j == 1, j == 3, j == 4)),
        And(i == 3, Or(j == 1, j == 2)),
        And(i == 4, Or(j == 1, j == 2))
    )

s.add(edge(c2, c3))
s.add(edge(c3, c4))
s.add(edge(c4, c5))

# Oslo constraint: must be in Oslo between day19 and day23
s.add(Or(
    And(c2 == 2, E2 >= 19),
    And(c3 == 2, E3 >= 19),
    And(c4 == 2, E4 >= 19),
    c5 == 2  # If Oslo is in stay5, no constraint needed
))

# Check for a solution
if s.check() == sat:
    model = s.model()
    E2_val = model[E2].as_long()
    E3_val = model[E3].as_long()
    E4_val = model[E4].as_long()
    c2_val = model[c2].as_long()
    c3_val = model[c3].as_long()
    c4_val = model[c4].as_long()
    c5_val = model[c5].as_long()
    
    city_names = {
        1: 'Paris',
        2: 'Oslo',
        3: 'Porto',
        4: 'Reykjavik'
    }
    
    itinerary = []
    for d in range(1, 24):
        if d < 7:
            cities = ['Geneva']
        elif d == 7:
            cities = ['Geneva', city_names[c2_val]]
        elif d < E2_val:
            cities = [city_names[c2_val]]
        elif d == E2_val:
            cities = [city_names[c2_val], city_names[c3_val]]
        elif d < E3_val:
            cities = [city_names[c3_val]]
        elif d == E3_val:
            cities = [city_names[c3_val], city_names[c4_val]]
        elif d < E4_val:
            cities = [city_names[c4_val]]
        elif d == E4_val:
            cities = [city_names[c4_val], city_names[c5_val]]
        else:  # d > E4_val and d <= 23
            cities = [city_names[c5_val]]
        
        itinerary.append({"day": d, "city": cities})
    
    result = {'itinerary': itinerary}
    print(json.dumps(result))
else:
    print('{"error": "No solution found"}')