import json
from z3 import *

def main():
    # Define cities as an enumerated data type
    City = Datatype('City')
    City.declare('Vilnius')
    City.declare('Split')
    City.declare('Madrid')
    City.declare('Santorini')
    City = City.create()
    vilnius, split, madrid, santorini = City.Vilnius, City.Split, City.Madrid, City.Santorini
    
    # Define direct flight connections (bidirectional)
    def has_direct_flight(c1, c2):
        return Or(
            And(c1 == vilnius, c2 == split),
            And(c1 == split, c2 == vilnius),
            And(c1 == split, c2 == madrid),
            And(c1 == madrid, c2 == split),
            And(c1 == madrid, c2 == santorini),
            And(c1 == santorini, c2 == madrid)
        )
    
    # Segment boundaries (start/end days)
    s1, e1 = Ints('s1 e1')
    s2, e2 = Ints('s2 e2')
    s3, e3 = Ints('s3 e3')
    s4, e4 = Ints('s4 e4')
    
    # City assignments for each segment
    c1, c2, c3, c4 = Consts('c1 c2 c3 c4', City)
    
    s = Solver()
    
    # Fixed constraints: trip starts day 1, ends day 14
    s.add(s1 == 1)
    s.add(e4 == 14)
    
    # Santorini must be on days 13-14 (last segment)
    s.add(s4 == 13, c4 == santorini)
    
    # Segment continuity: next segment starts where previous ends (flight day)
    s.add(s2 == e1)
    s.add(s3 == e2)
    s.add(s4 == e3)
    
    # Segment boundaries must be valid (1-14, non-empty, increasing)
    s.add(s1 >= 1, e1 <= 14, s1 <= e1)
    s.add(s2 >= 1, e2 <= 14, s2 <= e2)
    s.add(s3 >= 1, e3 <= 14, s3 <= e3)
    s.add(s4 >= 1, e4 <= 14, s4 <= e4)
    
    # Direct flights between consecutive segments
    s.add(has_direct_flight(c1, c2))
    s.add(has_direct_flight(c2, c3))
    s.add(has_direct_flight(c3, c4))
    
    # All cities must be visited (distinct)
    s.add(Distinct(c1, c2, c3, c4))
    
    # Calculate durations for each segment
    dur1 = e1 - s1 + 1
    dur2 = e2 - s2 + 1
    dur3 = e3 - s3 + 1
    dur4 = e4 - s4 + 1
    
    # Total days per city (accounting for flight days)
    total_vilnius = Sum([If(c1 == vilnius, dur1, 0), 
                         If(c2 == vilnius, dur2, 0),
                         If(c3 == vilnius, dur3, 0),
                         If(c4 == vilnius, dur4, 0)])
    
    total_split = Sum([If(c1 == split, dur1, 0), 
                      If(c2 == split, dur2, 0),
                      If(c3 == split, dur3, 0),
                      If(c4 == split, dur4, 0)])
    
    total_madrid = Sum([If(c1 == madrid, dur1, 0), 
                        If(c2 == madrid, dur2, 0),
                        If(c3 == madrid, dur3, 0),
                        If(c4 == madrid, dur4, 0)])
    
    total_santorini = Sum([If(c1 == santorini, dur1, 0), 
                           If(c2 == santorini, dur2, 0),
                           If(c3 == santorini, dur3, 0),
                           If(c4 == santorini, dur4, 0)])
    
    # Enforce stay duration constraints
    s.add(total_vilnius == 4)
    s.add(total_split == 5)
    s.add(total_madrid == 6)
    s.add(total_santorini == 2)
    
    # Find and output valid solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        # Collect segment information
        segments = [
            (s1, e1, c1),
            (s2, e2, c2),
            (s3, e3, c3),
            (s4, e4, c4)
        ]
        for seg in segments:
            start = m.eval(seg[0]).as_long()
            end = m.eval(seg[1]).as_long()
            city = m.eval(seg[2])
            city_name = str(city).split('=')[-1].strip(')')
            itinerary.append({
                "day_range": f"Day {start}-{end}",
                "place": city_name
            })
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()