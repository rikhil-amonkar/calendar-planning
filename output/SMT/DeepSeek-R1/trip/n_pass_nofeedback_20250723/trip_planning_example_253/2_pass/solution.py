from z3 import *
import json

def main():
    # City codes
    vienna = 0
    santorini = 1
    amsterdam = 2
    lyon = 3
    
    # Block variables
    b1, b2, b3, b4 = Ints('b1 b2 b3 b4')
    s = Solver()
    
    # Constraints: each block is a distinct city (0 to 3)
    s.add(b1 >= 0, b1 <= 3)
    s.add(b2 >= 0, b2 <= 3)
    s.add(b3 >= 0, b3 <= 3)
    s.add(b4 >= 0, b4 <= 3)
    s.add(Distinct(b1, b2, b3, b4))
    
    # Length of each block based on the city
    len1 = If(b1 == vienna, 7, If(b1 == santorini, 4, If(b1 == amsterdam, 3, 3)))
    len2 = If(b2 == vienna, 7, If(b2 == santorini, 4, If(b2 == amsterdam, 3, 3)))
    len3 = If(b3 == vienna, 7, If(b3 == santorini, 4, If(b3 == amsterdam, 3, 3)))
    len4 = If(b4 == vienna, 7, If(b4 == santorini, 4, If(b4 == amsterdam, 3, 3)))
    
    # End days for each block
    e1 = Int('e1')
    e2 = Int('e2')
    e3 = Int('e3')
    
    s.add(e1 == len1)
    s.add(e2 == e1 + len2 - 1)
    s.add(e3 == e2 + len3 - 1)
    s.add(e3 + len4 - 1 == 14)
    
    # Amsterdam must have at least one day in [9,11]
    ams_constraint = Or(
        And(b1 == amsterdam, e1 >= 9),
        And(b2 == amsterdam, e1 <= 11, e2 >= 9),
        And(b3 == amsterdam, e2 <= 11, e3 >= 9),
        And(b4 == amsterdam, e3 <= 11)
    )
    s.add(ams_constraint)
    
    # Lyon must have at least one day in [7,9]
    lyon_constraint = Or(
        And(b1 == lyon, e1 >= 7),
        And(b2 == lyon, e1 <= 9, e2 >= 7),
        And(b3 == lyon, e2 <= 9, e3 >= 7),
        And(b4 == lyon, e3 <= 9)
    )
    s.add(lyon_constraint)
    
    # Define allowed direct flights (both directions)
    allowed_edges = [
        (vienna, lyon),
        (vienna, santorini),
        (vienna, amsterdam),
        (amsterdam, santorini),
        (amsterdam, lyon)
    ]
    
    # Function to check if two cities are connected by a direct flight
    def connected(c1, c2):
        conditions = []
        for (i, j) in allowed_edges:
            conditions.append(And(c1 == i, c2 == j))
            conditions.append(And(c1 == j, c2 == i))
        return Or(conditions)
    
    # Consecutive blocks must be connected by direct flights
    s.add(connected(b1, b2))
    s.add(connected(b2, b3))
    s.add(connected(b3, b4))
    
    # Solve the model
    if s.check() == sat:
        m = s.model()
        b1_val = m[b1].as_long()
        b2_val = m[b2].as_long()
        b3_val = m[b3].as_long()
        b4_val = m[b4].as_long()
        e1_val = m[e1].as_long()
        e2_val = m[e2].as_long()
        e3_val = m[e3].as_long()
        
        city_names = {
            vienna: "Vienna",
            santorini: "Santorini",
            amsterdam: "Amsterdam",
            lyon: "Lyon"
        }
        
        itinerary = []
        for day in range(1, 15):
            if day <= e1_val:
                itinerary.append({"day": day, "city": city_names[b1_val]})
            if day >= e1_val and day <= e2_val:
                itinerary.append({"day": day, "city": city_names[b2_val]})
            if day >= e2_val and day <= e3_val:
                itinerary.append({"day": day, "city": city_names[b3_val]})
            if day >= e3_val:
                itinerary.append({"day": day, "city": city_names[b4_val]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()