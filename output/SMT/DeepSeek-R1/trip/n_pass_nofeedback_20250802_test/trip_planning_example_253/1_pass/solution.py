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
    
    # Start and end days for each block
    s1 = 1
    e1 = s1 + len1 - 1
    s2 = e1
    e2 = s2 + len2 - 1
    s3 = e2
    e3 = s3 + len3 - 1
    s4 = e3
    e4 = s4 + len4 - 1  # Should be 14
    
    # Amsterdam must have at least one day in [9,11]
    ams_constraint = Or(
        And(b1 == amsterdam, s1 <= 11, e1 >= 9),
        And(b2 == amsterdam, s2 <= 11, e2 >= 9),
        And(b3 == amsterdam, s3 <= 11, e3 >= 9),
        And(b4 == amsterdam, s4 <= 11, e4 >= 9)
    )
    s.add(ams_constraint)
    
    # Lyon must have at least one day in [7,9]
    lyon_constraint = Or(
        And(b1 == lyon, s1 <= 9, e1 >= 7),
        And(b2 == lyon, s2 <= 9, e2 >= 7),
        And(b3 == lyon, s3 <= 9, e3 >= 7),
        And(b4 == lyon, s4 <= 9, e4 >= 7)
    )
    s.add(lyon_constraint)
    
    # Connectivity constraints: consecutive cities must have direct flights
    def connected(c1, c2):
        return Or(
            And(c1 == vienna, c2 == santorini),
            And(c1 == vienna, c2 == amsterdam),
            And(c1 == vienna, c2 == lyon),
            And(c1 == santorini, c2 == vienna),
            And(c1 == santorini, c2 == amsterdam),
            And(c1 == amsterdam, c2 == vienna),
            And(c1 == amsterdam, c2 == santorini),
            And(c1 == amsterdam, c2 == lyon),
            And(c1 == lyon, c2 == vienna),
            And(c1 == lyon, c2 == amsterdam)
        )
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
        
        len1_val = m.evaluate(len1).as_long()
        len2_val = m.evaluate(len2).as_long()
        len3_val = m.evaluate(len3).as_long()
        len4_val = m.evaluate(len4).as_long()
        
        s1_val = 1
        e1_val = s1_val + len1_val - 1
        s2_val = e1_val
        e2_val = s2_val + len2_val - 1
        s3_val = e2_val
        e3_val = s3_val + len3_val - 1
        s4_val = e3_val
        e4_val = s4_val + len4_val - 1
        
        city_names = {
            vienna: "Vienna",
            santorini: "Santorini",
            amsterdam: "Amsterdam",
            lyon: "Lyon"
        }
        
        itinerary = []
        for day in range(1, 15):
            if day >= s1_val and day <= e1_val:
                itinerary.append({"day": day, "city": city_names[b1_val]})
            if day >= s2_val and day <= e2_val:
                itinerary.append({"day": day, "city": city_names[b2_val]})
            if day >= s3_val and day <= e3_val:
                itinerary.append({"day": day, "city": city_names[b3_val]})
            if day >= s4_val and day <= e4_val:
                itinerary.append({"day": day, "city": city_names[b4_val]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()