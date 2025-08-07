import json
from z3 import *

def main():
    # Define the cities
    City, (vilnius, split, madrid, santorini) = EnumSort('City', ['Vilnius', 'Split', 'Madrid', 'Santorini'])
    
    # Define direct flight connections (bidirectional)
    connections = [
        (vilnius, split),
        (split, vilnius),
        (split, madrid),
        (madrid, split),
        (madrid, santorini),
        (santorini, madrid)
    ]
    
    def connected(c1, c2):
        return Or([And(c1 == a, c2 == b) for (a, b) in connections])
    
    # Segment boundaries and city assignments
    s1, e1, s2, e2, s3, e3, s4, e4 = Ints('s1 e1 s2 e2 s3 e3 s4 e4')
    c1, c2, c3, c4 = Consts('c1 c2 c3 c4', City)
    
    s = Solver()
    
    # Fixed constraints: start day 1, end day 14
    s.add(s1 == 1)
    s.add(e4 == 14)
    
    # Contiguous segments
    s.add(e1 == s2, e2 == s3, e3 == s4)
    
    # Non-negative segment durations
    s.add(e1 >= s1, e2 >= s2, e3 >= s3, e4 >= s4)
    
    # Last segment must be Santorini
    s.add(c4 == santorini)
    
    # Durations for each segment
    dur1 = e1 - s1 + 1
    dur2 = e2 - s2 + 1
    dur3 = e3 - s3 + 1
    dur4 = e4 - s4 + 1
    
    # Total days per city
    total_vilnius = If(c1 == vilnius, dur1, 0) + If(c2 == vilnius, dur2, 0) + If(c3 == vilnius, dur3, 0) + If(c4 == vilnius, dur4, 0)
    total_split   = If(c1 == split,   dur1, 0) + If(c2 == split,   dur2, 0) + If(c3 == split,   dur3, 0) + If(c4 == split,   dur4, 0)
    total_madrid  = If(c1 == madrid,  dur1, 0) + If(c2 == madrid,  dur2, 0) + If(c3 == madrid,  dur3, 0) + If(c4 == madrid,  dur4, 0)
    total_santorini = If(c1 == santorini, dur1, 0) + If(c2 == santorini, dur2, 0) + If(c3 == santorini, dur3, 0) + If(c4 == santorini, dur4, 0)
    
    s.add(total_vilnius == 4)
    s.add(total_split == 5)
    s.add(total_madrid == 6)
    s.add(total_santorini == 2)
    
    # Flight constraints: consecutive cities must have direct flights
    s.add(connected(c1, c2))
    s.add(connected(c2, c3))
    s.add(connected(c3, c4))
    
    # All cities must be distinct
    s.add(Distinct(c1, c2, c3, c4))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Build the itinerary segments
        seg1 = {
            "city": str(m.eval(c1)),
            "start_day": m.eval(s1).as_long(),
            "end_day": m.eval(e1).as_long()
        }
        seg2 = {
            "city": str(m.eval(c2)),
            "start_day": m.eval(s2).as_long(),
            "end_day": m.eval(e2).as_long()
        }
        seg3 = {
            "city": str(m.eval(c3)),
            "start_day": m.eval(s3).as_long(),
            "end_day": m.eval(e3).as_long()
        }
        seg4 = {
            "city": str(m.eval(c4)),
            "start_day": m.eval(s4).as_long(),
            "end_day": m.eval(e4).as_long()
        }
        itinerary = [seg1, seg2, seg3, seg4]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()