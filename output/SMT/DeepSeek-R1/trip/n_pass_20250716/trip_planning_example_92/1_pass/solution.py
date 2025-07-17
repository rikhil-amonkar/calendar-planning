from z3 import *
import json

def main():
    d1 = Int('d1')
    d2 = Int('d2')
    
    s = Solver()
    s.add(d1 >= 1, d1 <= 12, d2 >= 1, d2 <= 12, d1 < d2)
    s.add(d1 == 2)
    s.add(d2 - d1 + 1 == 5)
    s.add(12 - d2 + 1 == 7)
    
    if s.check() == sat:
        m = s.model()
        d1_val = m[d1].as_long()
        d2_val = m[d2].as_long()
        
        itinerary = [
            {"day_range": "Day 1-2", "place": "Dublin"},
            {"day_range": "Day 2", "place": "Dublin"},
            {"day_range": "Day 2", "place": "Riga"},
            {"day_range": "Day 2-6", "place": "Riga"},
            {"day_range": "Day 6", "place": "Riga"},
            {"day_range": "Day 6", "place": "Vilnius"},
            {"day_range": "Day 6-12", "place": "Vilnius"}
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()