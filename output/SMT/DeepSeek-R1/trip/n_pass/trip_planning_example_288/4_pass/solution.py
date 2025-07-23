from z3 import *
import json

def main():
    s = Solver()
    
    # Days for transitions
    a = Int('a')
    b = Int('b')
    c = Int('c')
    
    # Segment assignments: 0=Manchester, 1=Stuttgart, 2=Madrid, 3=Vienna
    seg1 = Int('seg1')
    seg2 = Int('seg2')
    seg3 = Int('seg3')
    seg4 = Int('seg4')
    
    # Constraints: 1<=a<=b<=c<=15
    s.add(a >= 1, a <= 15)
    s.add(b >= a, b <= 15)
    s.add(c >= b, c <= 15)
    
    # Each segment variable is an integer between 0 and 3
    s.add(seg1 >= 0, seg1 <= 3)
    s.add(seg2 >= 0, seg2 <= 3)
    s.add(seg3 >= 0, seg3 <= 3)
    s.add(seg4 >= 0, seg4 <= 3)
    s.add(Distinct(seg1, seg2, seg3, seg4))
    
    # Required days for each city: [Manchester, Stuttgart, Madrid, Vienna]
    reqs = [7, 5, 4, 2]
    
    # Helper function to get required days for a segment
    def get_req(seg):
        return If(seg == 0, reqs[0],
               If(seg == 1, reqs[1],
               If(seg == 2, reqs[2],
               reqs[3])))
    
    # Segment lengths must match city requirements
    s.add(a == get_req(seg1))
    s.add(b - a + 1 == get_req(seg2))
    s.add(c - b + 1 == get_req(seg3))
    s.add(16 - c == get_req(seg4))
    
    # Direct flight constraints
    def edge_ok(x, y):
        return Or(
            And(x == 0, y == 1), And(x == 1, y == 0),
            And(x == 0, y == 2), And(x == 2, y == 0),
            And(x == 0, y == 3), And(x == 3, y == 0),
            And(x == 1, y == 3), And(x == 3, y == 1),
            And(x == 2, y == 3), And(x == 3, y == 2)
        )
    
    s.add(edge_ok(seg1, seg2))
    s.add(edge_ok(seg2, seg3))
    s.add(edge_ok(seg3, seg4))
    
    # Event constraints
    # Manchester (0) must have at least one day in [1,7]
    manchester_constraint = Or(
        And(seg1 == 0, a >= 1),  # seg1 covers [1, a] and includes day 1
        And(seg2 == 0, a <= 7),   # seg2 covers [a, b]; must start by day 7
        And(seg3 == 0, b <= 7),   # seg3 covers [b, c]; must start by day 7
        And(seg4 == 0, c <= 7)    # seg4 covers [c,15]; must start by day 7
    )
    s.add(manchester_constraint)
    
    # Stuttgart (1) must have at least one day in [11,15]
    stuttgart_constraint = Or(
        And(seg1 == 1, a >= 11),  # seg1 must extend to day 11+
        And(seg2 == 1, b >= 11),   # seg2 must extend to day 11+
        And(seg3 == 1, c >= 11),   # seg3 must extend to day 11+
        And(seg4 == 1, c <= 15)    # seg4 always includes day 15
    )
    s.add(stuttgart_constraint)
    
    if s.check() == sat:
        m = s.model()
        a_val = m[a].as_long()
        b_val = m[b].as_long()
        c_val = m[c].as_long()
        seg1_val = m[seg1].as_long()
        seg2_val = m[seg2].as_long()
        seg3_val = m[seg3].as_long()
        seg4_val = m[seg4].as_long()
        
        city_names = {
            0: "Manchester",
            1: "Stuttgart",
            2: "Madrid",
            3: "Vienna"
        }
        
        itinerary = []
        for d in range(1, 16):
            places = []
            if d <= a_val:
                places.append(city_names[seg1_val])
            if d >= a_val and d <= b_val:
                places.append(city_names[seg2_val])
            if d >= b_val and d <= c_val:
                places.append(city_names[seg3_val])
            if d >= c_val:
                places.append(city_names[seg4_val])
            itinerary.append({"day": d, "place": places})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()