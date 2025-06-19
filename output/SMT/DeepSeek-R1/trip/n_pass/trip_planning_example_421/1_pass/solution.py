import json
from z3 import *

def main():
    d2 = Int('d2')
    d3 = Int('d3')
    s1 = Int('s1')
    s2 = Int('s2')
    s3 = Int('s3')
    
    s = Solver()
    
    s.add(d2 > 5, d2 < 19)
    s.add(d3 > d2, d3 < 19)
    
    dur1 = d2 - 4
    dur2 = d3 - d2 + 1
    dur3 = 20 - d3
    
    s.add(dur1 > 0, dur2 > 0, dur3 > 0)
    
    s.add(Distinct(s1, s2, s3))
    s.add(s1 >= 1, s1 <= 3)
    s.add(s2 >= 1, s2 <= 3)
    s.add(s3 >= 1, s3 <= 3)
    
    dur_s1 = If(s1 == 1, 7, If(s1 == 2, 6, 4))
    dur_s2 = If(s2 == 1, 7, If(s2 == 2, 6, 4))
    dur_s3 = If(s3 == 1, 7, If(s3 == 2, 6, 4))
    
    s.add(dur1 == dur_s1)
    s.add(dur2 == dur_s2)
    s.add(dur3 == dur_s3)
    
    s.add(Or(s1 == 1, s1 == 3))
    
    s.add(Or(
        And(s1 == 1, Or(s2 == 2, s2 == 3)),
        And(s1 == 3, s2 == 1)
    ))
    
    s.add(Or(
        And(s2 == 1, Or(s3 == 2, s3 == 3)),
        And(s2 == 2, s3 == 1),
        And(s2 == 3, s3 == 1)
    ))
    
    if s.check() == sat:
        m = s.model()
        d2_val = m[d2].as_long()
        d3_val = m[d3].as_long()
        s1_val = m[s1].as_long()
        s2_val = m[s2].as_long()
        s3_val = m[s3].as_long()
        
        city_names = {
            0: "Nice",
            1: "Dublin",
            2: "Krakow",
            3: "Lyon",
            4: "Frankfurt"
        }
        
        segments = [
            (1, 5, 0),
            (5, d2_val, s1_val),
            (d2_val, d3_val, s2_val),
            (d3_val, 19, s3_val),
            (19, 20, 4)
        ]
        
        itinerary = []
        
        for i, seg in enumerate(segments):
            start, end, city_idx = seg
            city = city_names[city_idx]
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": city})
            
            if i < len(segments) - 1:
                next_city_idx = segments[i+1][2]
                next_city = city_names[next_city_idx]
                itinerary.append({"day_range": f"Day {end}", "place": city})
                itinerary.append({"day_range": f"Day {end}", "place": next_city})
                
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()