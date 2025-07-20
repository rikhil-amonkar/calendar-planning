from z3 import *
import json

def main():
    f1 = Int('f1')
    f2 = Int('f2')
    
    s = Solver()
    s.add(f1 >= 1, f1 <= 12)
    s.add(f2 >= 1, f2 <= 12)
    s.add(f1 < f2)
    s.add(f1 == 4)
    s.add(f2 - f1 + 1 == 3)
    s.add(12 - f2 + 1 == 7)
    
    itinerary = []
    if s.check() == sat:
        m = s.model()
        f1_val = m[f1].as_long()
        f2_val = m[f2].as_long()
        
        if f1_val > 1:
            itinerary.append({"day_range": f"Day 1-{f1_val-1}", "place": "Vilnius"})
        itinerary.append({"day_range": f"Day {f1_val}", "place": "Vilnius"})
        
        itinerary.append({"day_range": f"Day {f1_val}", "place": "Munich"})
        
        itinerary.append({"day_range": f"Day {f1_val}-{f2_val}", "place": "Munich"})
        itinerary.append({"day_range": f"Day {f2_val}", "place": "Munich"})
        
        itinerary.append({"day_range": f"Day {f2_val}", "place": "Mykonos"})
        
        if f2_val < 12:
            itinerary.append({"day_range": f"Day {f2_val}-12", "place": "Mykonos"})
        else:
            itinerary.append({"day_range": f"Day {f2_val}", "place": "Mykonos"})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No valid itinerary found.")

if __name__ == "__main__":
    main()