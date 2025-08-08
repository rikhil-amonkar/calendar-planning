from z3 import *
import json

def main():
    city_names = {0: "Manchester", 1: "Stuttgart", 2: "Madrid", 3: "Vienna"}
    edges = [(0, 1), (0, 2), (0, 3), (1, 3), (2, 3)]  # Direct flight connections
    
    # Segment cities and end days
    c1, c2, c3, c4 = Ints('c1 c2 c3 c4')
    e1, e2, e3 = Ints('e1 e2 e3')
    
    s = Solver()
    
    # Cities must be distinct and in 0-3
    s.add([And(c >= 0, c <= 3) for c in [c1, c2, c3, c4]])
    s.add(Distinct(c1, c2, c3, c4))
    
    # End days must be ordered: 1 <= e1 < e2 < e3 <= 15
    s.add(e1 >= 1, e1 <= 15)
    s.add(e2 > e1, e2 <= 15)
    s.add(e3 > e2, e3 <= 15)
    
    # Flight connections between consecutive segments
    def flight_ok(a, b):
        return Or([Or(And(a == i, b == j), And(a == j, b == i)) for (i,j) in edges])
    s.add(flight_ok(c1, c2))
    s.add(flight_ok(c2, c3))
    s.add(flight_ok(c3, c4))
    
    # Day count constraints
    def days_in_city(city):
        return If(c1 == city, e1,
                If(c2 == city, e2 - e1,
                If(c3 == city, e3 - e2,
                15 - e3 + 1)))  # +1 because last segment includes e3 day
    s.add(days_in_city(0) == 7)  # Manchester
    s.add(days_in_city(1) == 5)  # Stuttgart
    s.add(days_in_city(2) == 4)  # Madrid
    s.add(days_in_city(3) == 2)  # Vienna
    
    # Manchester wedding constraint (at least one day in 1-7)
    s.add(Or(
        And(c1 == 0, e1 >= 1),   # Entirely in 1-7
        And(c2 == 0, e1 <= 7, e2 >= 1),  # Overlaps 1-7
        And(c3 == 0, e2 <= 7, e3 >= 1),
        And(c4 == 0, e3 <= 7)
    ))
    
    # Stuttgart workshop constraint (must cover 11-15)
    stuttgart_in_segment = []
    stuttgart_in_segment.append(And(c1 == 1, e1 >= 11))        # Segment1 covers 11+
    stuttgart_in_segment.append(And(c2 == 1, e1 <= 15, e2 >= 11)) # Segment2 overlaps [11,15]
    stuttgart_in_segment.append(And(c3 == 1, e2 <= 15, e3 >= 11)) # Segment3 overlaps [11,15]
    stuttgart_in_segment.append(And(c4 == 1, e3 <= 15))        # Segment4 covers until 15
    s.add(Or(stuttgart_in_segment))
    
    # Block previous invalid solution
    s.add(Not(And(
        c1 == 2,  # Madrid first
        c2 == 0,  # Manchester second
        c3 == 3,  # Vienna third
        c4 == 1,  # Stuttgart last
        e1 == 4,
        e2 == 10,
        e3 == 11
    )))
    
    if s.check() == sat:
        m = s.model()
        c1_val = m[c1].as_long()
        c2_val = m[c2].as_long()
        c3_val = m[c3].as_long()
        c4_val = m[c4].as_long()
        e1_val = m[e1].as_long()
        e2_val = m[e2].as_long()
        e3_val = m[e3].as_long()
        
        # Build itinerary in day-range format
        itinerary = [
            {"day_range": f"Day 1-{e1_val}", "place": city_names[c1_val]},
            {"day_range": f"Day {e1_val}-{e2_val}", "place": city_names[c2_val]},
            {"day_range": f"Day {e2_val}-{e3_val}", "place": city_names[c3_val]},
            {"day_range": f"Day {e3_val}-15", "place": city_names[c4_val]}
        ]
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No valid solution found")

if __name__ == "__main__":
    main()