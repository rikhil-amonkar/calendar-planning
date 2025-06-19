import json
from z3 import *

def main():
    d1 = Int('d1')
    d2 = Int('d2')
    
    s = Solver()
    s.add(d1 >= 2, d1 <= 12)
    s.add(d2 >= d1, d2 <= 12)
    s.add(d1 == 2)
    s.add(d2 - d1 + 1 == 7)
    s.add(12 - d2 + 1 == 5)
    
    if s.check() == sat:
        m = s.model()
        d1_val = m[d1].as_long()
        d2_val = m[d2].as_long()
        
        def format_day_range(start, end):
            if start == end:
                return f"Day {start}"
            else:
                return f"Day {start}-{end}"
        
        itinerary_list = [
            {"day_range": format_day_range(1, d1_val), "place": "Brussels"},
            {"day_range": f"Day {d1_val}", "place": "Brussels"},
            {"day_range": f"Day {d1_val}", "place": "Barcelona"},
            {"day_range": format_day_range(d1_val, d2_val), "place": "Barcelona"},
            {"day_range": f"Day {d2_val}", "place": "Barcelona"},
            {"day_range": f"Day {d2_val}", "place": "Split"},
            {"day_range": format_day_range(d2_val, 12), "place": "Split"}
        ]
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()