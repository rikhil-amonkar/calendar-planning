import json
from z3 import *

def main():
    # Define the cities
    City = Datatype('City')
    City.declare('Vilnius')
    City.declare('Split')
    City.declare('Madrid')
    City.declare('Santorini')
    City = City.create()
    vilnius = City.Vilnius
    split = City.Split
    madrid = City.Madrid
    santorini = City.Santorini

    # Define direct flight connections
    def direct_flight(c1, c2):
        return Or(
            And(c1 == vilnius, c2 == split),
            And(c1 == split, c2 == vilnius),
            And(c1 == split, c2 == madrid),
            And(c1 == madrid, c2 == split),
            And(c1 == madrid, c2 == santorini),
            And(c1 == santorini, c2 == madrid)
        )
    
    # Segment boundaries and city assignments
    s1, e1, s2, e2, s3, e3, s4, e4 = Ints('s1 e1 s2 e2 s3 e3 s4 e4')
    c1, c2, c3, c4 = Consts('c1 c2 c3 c4', City)
    
    s = Solver()
    
    # Fixed constraints: start day 1, end day 14, and Santorini on days 13-14
    s.add(s1 == 1)
    s.add(e4 == 14)
    s.add(s4 == 13, c4 == santorini)  # Santorini must be on days 13 and 14
    
    # Contiguous segments: flight day is the same as the next segment's start day
    s.add(s2 == e1, s3 == e2, s4 == e3)
    
    # Ensure segments are non-empty and increasing
    s.add(s1 <= e1, s2 <= e2, s3 <= e3, s4 <= e4)
    s.add(e1 >= 1, e2 >= 1, e3 >= 1, e1 <= 14, e2 <= 14, e3 <= 14)
    
    # Flight connections between consecutive segments
    s.add(direct_flight(c1, c2))
    s.add(direct_flight(c2, c3))
    s.add(direct_flight(c3, c4))
    
    # All cities must be distinct
    s.add(Distinct(c1, c2, c3, c4))
    
    # Calculate durations for each segment
    dur1 = e1 - s1 + 1
    dur2 = e2 - s2 + 1
    dur3 = e3 - s3 + 1
    dur4 = e4 - s4 + 1
    
    # Total days per city
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
    
    s.add(total_vilnius == 4)
    s.add(total_split == 5)
    s.add(total_madrid == 6)
    s.add(total_santorini == 2)  # Already enforced by s4=13 and e4=14, but added for clarity
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        seg_vars = [(s1, e1, c1), (s2, e2, c2), (s3, e3, c3), (s4, e4, c4)]
        for i, (start, end, city) in enumerate(seg_vars):
            start_val = m.eval(start).as_long()
            end_val = m.eval(end).as_long()
            city_val = m.eval(city)
            city_name = str(city_val).split('=')[-1].strip(')')
            itinerary.append({
                "city": city_name,
                "start_day": start_val,
                "end_day": end_val
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()