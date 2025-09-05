import json
from z3 import *

def main():
    s = Solver()
    
    # We use indices to represent cities:
    # 0: Madrid (4 days)
    # 1: Seville (2 days)
    # 2: Porto (3 days)
    # 3: Stuttgart (7 days)
    #
    # We assume the itinerary is split into 4 segments.
    # Because of flight overlaps, the total days equals
    # (d1 + d2 + d3 + d4) - 3, which must equal 13.
    
    # Define city variables for each segment.
    p0 = Int('p0')
    p1 = Int('p1')
    p2 = Int('p2')
    p3 = Int('p3')
    
    # Domain restrictions.
    # As argued below, Stuttgart (3) must be last.
    s.add(p3 == 3)
    # For the flight into Stuttgart to be allowed, p2 must be Porto (2)
    s.add(p2 == 2)
    # p0 and p1 will be Madrid (0) and Seville (1) in some order.
    s.add(Or(p0 == 0, p0 == 1))
    s.add(Or(p1 == 0, p1 == 1))
    s.add(Distinct(p0, p1, p2, p3))
    
    # Define a function to give duration based on city.
    def duration(city):
        return If(city == 0, 4, If(city == 1, 2, If(city == 2, 3, If(city == 3, 7, -1))))
    
    d0 = duration(p0)
    d1 = duration(p1)
    d2 = duration(p2)
    d3 = duration(p3)
    
    # Total days: (d0 + d1 + d2 + d3) - 3 = 13
    s.add(d0 + d1 + d2 + d3 == 16)
    s.add(d0 + d1 + d2 + d3 - 3 == 13)
    
    # Allowed direct flights:
    # Flight from segment1 to segment2 must be between Madrid and Seville.
    s.add(Or(And(p0 == 0, p1 == 1), And(p0 == 1, p1 == 0)))
    # Flight from segment2 to segment3: flight from Madrid or Seville to Porto.
    s.add(Or(And(p1 == 0, p2 == 2), And(p1 == 1, p2 == 2)))
    # Flight from segment3 to segment4: only Porto <-> Stuttgart is allowed.
    s.add(And(p2 == 2, p3 == 3))
    
    # Relatives in Madrid constraint:
    # You plan to visit relatives in Madrid between day 1 and day 4.
    # If segment 1 lasts at least 4 days, then day 1-4 lie entirely in seg1,
    # so p0 must be Madrid. Otherwise seg1 is shorter than 4 days and seg2
    # covers an early day, so p1 must be Madrid.
    s.add(If(d0 >= 4, p0 == 0, p1 == 0))
    
    # Compute segment boundaries.
    # Segment 1: Day 1 to b1 = d0.
    # Segment 2: Day b1 to b2 = d0 + d1 - 1.
    # Segment 3: Day b2 to b3 = d0 + d1 + d2 - 2.
    # Segment 4: Day b3 to Day 13.
    b1 = d0
    b2 = d0 + d1 - 1
    b3 = d0 + d1 + d2 - 2
    
    # Conference in Stuttgart on Day 7 and Day 13.
    # Day 13 is automatically in segment 4 (p3==3) so we only set a constraint for Day 7.
    # On a flight day, you are in both the departing and arriving city.
    # We require that on Day 7 at least one of the segments covering that day corresponds to Stuttgart.
    conf_day7 = If(7 < b1,
                    p0 == 3,
                    If(7 == b1,
                       Or(p0 == 3, p1 == 3),
                       If(7 < b2,
                          p1 == 3,
                          If(7 == b2,
                             Or(p1 == 3, p2 == 3),
                             If(7 < b3,
                                p2 == 3,
                                If(7 == b3,
                                   Or(p2 == 3, p3 == 3),
                                   p3 == 3  # 7 > b3
                                   )))))
    s.add(conf_day7)
    
    if s.check() == sat:
        m = s.model()
        seg_d0 = m.evaluate(d0).as_long()
        seg_d1 = m.evaluate(d1).as_long()
        seg_d2 = m.evaluate(d2).as_long()
        seg_d3 = m.evaluate(d3).as_long()
        
        # Calculate segment day ranges.
        seg1_start = 1
        seg1_end = seg1_start + seg_d0 - 1
        seg2_start = seg1_end
        seg2_end = seg2_start + seg_d1 - 1
        seg3_start = seg2_end
        seg3_end = seg3_start + seg_d2 - 1
        seg4_start = seg3_end
        seg4_end = 13  # by construction
        
        city_names = {0: "Madrid", 1: "Seville", 2: "Porto", 3: "Stuttgart"}
        
        itinerary = []
        itinerary.append({
            "day_range": f"Day {seg1_start}-{seg1_end}",
            "place": city_names[m.evaluate(p0).as_long()]
        })
        itinerary.append({
            "day_range": f"Day {seg2_start}-{seg2_end}",
            "place": city_names[m.evaluate(p1).as_long()]
        })
        itinerary.append({
            "day_range": f"Day {seg3_start}-{seg3_end}",
            "place": city_names[m.evaluate(p2).as_long()]
        })
        itinerary.append({
            "day_range": f"Day {seg4_start}-{seg4_end}",
            "place": city_names[m.evaluate(p3).as_long()]
        })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()