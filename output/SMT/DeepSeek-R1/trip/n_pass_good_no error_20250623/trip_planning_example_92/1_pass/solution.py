import json
from z3 import *

def main():
    d_start = Int('d_start')
    r_start = Int('r_start')
    r_end = Int('r_end')
    
    s = Solver()
    s.add(d_start >= 1)
    s.add(r_end <= 12)
    s.add(r_start - d_start + 1 == 2)
    s.add(r_end - r_start + 1 == 5)
    s.add(12 - r_end + 1 == 7)
    
    if s.check() == sat:
        m = s.model()
        d_start_val = m[d_start].as_long()
        r_start_val = m[r_start].as_long()
        r_end_val = m[r_end].as_long()
        
        itinerary = [
            {"day_range": f"Day {d_start_val}-{r_start_val}", "place": "Dublin"},
            {"day_range": f"Day {r_start_val}", "place": "Dublin"},
            {"day_range": f"Day {r_start_val}", "place": "Riga"},
            {"day_range": f"Day {r_start_val}-{r_end_val}", "place": "Riga"},
            {"day_range": f"Day {r_end_val}", "place": "Riga"},
            {"day_range": f"Day {r_end_val}", "place": "Vilnius"},
            {"day_range": f"Day {r_end_val}-12", "place": "Vilnius"}
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()