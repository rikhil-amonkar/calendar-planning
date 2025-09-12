import json
from z3 import *

def main():
    # Cities mapping: Istanbul=0, Rome=1, Seville=2, Naples=3, Santorini=4
    cities = ["Istanbul", "Rome", "Seville", "Naples", "Santorini"]
    
    # Direct flights (undirected)
    allowed_edges = [
        (0, 1), (0, 3), 
        (1, 0), (1, 2), (1, 3), (1, 4),
        (2, 1),
        (3, 0), (3, 1), (3, 4),
        (4, 1), (4, 3)
    ]
    
    s = Solver()
    
    # Segment end days
    a = Int('a')
    b = Int('b')
    c = Int('c')
    d = Int('d')
    
    # Constraints on segment days
    s.add(1 <= a, a < b, b < c, c < d, d <= 15)
    
    # Segment city assignments
    seg1 = Int('seg1')
    seg2 = Int('seg2')
    seg3 = Int('seg3')
    seg4 = Int('seg4')
    seg5 = Int('seg5')
    
    # Each segment is one of the cities
    s.add(And(seg1 >= 0, seg1 <= 4))
    s.add(And(seg2 >= 0, seg2 <= 4))
    s.add(And(seg3 >= 0, seg3 <= 4))
    s.add(And(seg4 >= 0, seg4 <= 4))
    s.add(And(seg5 >= 0, seg5 <= 4))
    
    # All segments assigned to distinct cities
    s.add(Distinct(seg1, seg2, seg3, seg4, seg5))
    
    # Direct flight constraints between consecutive segments
    s.add(Or(*[And(seg1 == x, seg2 == y) for x, y in allowed_edges if x != y]))
    s.add(Or(*[And(seg2 == x, seg3 == y) for x, y in allowed_edges if x != y]))
    s.add(Or(*[And(seg3 == x, seg4 == y) for x, y in allowed_edges if x != y]))
    s.add(Or(*[And(seg4 == x, seg5 == y) for x, y in allowed_edges if x != y]))
    
    # Desired days per city
    desired_days = {
        0: 2,  # Istanbul
        1: 3,  # Rome
        2: 4,  # Seville
        3: 7,  # Naples
        4: 4   # Santorini
    }
    
    # Segment length constraints
    s.add(If(seg1 == 0, a == desired_days[0], 
          If(seg1 == 1, a == desired_days[1],
          If(seg1 == 2, a == desired_days[2],
          If(seg1 == 3, a == desired_days[3],
          If(seg1 == 4, a == desired_days[4], False))))))
    
    s.add(If(seg2 == 0, (b - a + 1) == desired_days[0],
          If(seg2 == 1, (b - a + 1) == desired_days[1],
          If(seg2 == 2, (b - a + 1) == desired_days[2],
          If(seg2 == 3, (b - a + 1) == desired_days[3],
          If(seg2 == 4, (b - a + 1) == desired_days[4], False))))))
    
    s.add(If(seg3 == 0, (c - b + 1) == desired_days[0],
          If(seg3 == 1, (c - b + 1) == desired_days[1],
          If(seg3 == 2, (c - b + 1) == desired_days[2],
          If(seg3 == 3, (c - b + 1) == desired_days[3],
          If(seg3 == 4, (c - b + 1) == desired_days[4], False))))))
    
    s.add(If(seg4 == 0, (d - c + 1) == desired_days[0],
          If(seg4 == 1, (d - c + 1) == desired_days[1],
          If(seg4 == 2, (d - c + 1) == desired_days[2],
          If(seg4 == 3, (d - c + 1) == desired_days[3],
          If(seg4 == 4, (d - c + 1) == desired_days[4], False))))))
    
    s.add(If(seg5 == 0, (16 - d + 1) == desired_days[0],
          If(seg5 == 1, (16 - d + 1) == desired_days[1],
          If(seg5 == 2, (16 - d + 1) == desired_days[2],
          If(seg5 == 3, (16 - d + 1) == desired_days[3],
          If(seg5 == 4, (16 - d + 1) == desired_days[4], False))))))
    
    # Istanbul must include days 6 and 7
    s.add(Or(
        And(seg1 == 0, a >= 7), 
        And(seg2 == 0, a <= 6, b >= 7),
        And(seg3 == 0, b <= 6, c >= 7),
        And(seg4 == 0, c <= 6, d >= 7),
        And(seg5 == 0, d <= 6)
    ))
    
    # Santorini must include days 13,14,15,16 -> must be in seg5
    s.add(seg5 == 4)
    s.add(d == 13)  # Because 16 - d + 1 = 4 => d=13
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        a_val = m[a].as_long()
        b_val = m[b].as_long()
        c_val = m[c].as_long()
        d_val = m[d].as_long()
        seg1_val = m[seg1].as_long()
        seg2_val = m[seg2].as_long()
        seg3_val = m[seg3].as_long()
        seg4_val = m[seg4].as_long()
        seg5_val = m[seg5].as_long()
        
        segments = [
            (1, a_val, seg1_val),
            (a_val, b_val, seg2_val),
            (b_val, c_val, seg3_val),
            (c_val, d_val, seg4_val),
            (d_val, 16, seg5_val)
        ]
        
        itinerary = []
        for start, end, city_idx in segments:
            city = cities[city_idx]
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No solution found')

if __name__ == "__main__":
    main()