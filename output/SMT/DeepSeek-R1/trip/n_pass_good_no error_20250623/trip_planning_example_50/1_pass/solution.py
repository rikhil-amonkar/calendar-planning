from z3 import Int, Solver, sat
import json

def main():
    F1 = Int('F1')
    F2 = Int('F2')
    s = Solver()
    s.add(F1 >= 1, F1 <= 12)
    s.add(F2 >= 1, F2 <= 12)
    s.add(F1 < F2)
    s.add(F1 == 4)
    s.add(F2 - F1 + 1 == 3)
    s.add(12 - F2 + 1 == 7)
    
    if s.check() == sat:
        m = s.model()
        f1 = m[F1].as_long()
        f2 = m[F2].as_long()
        
        itinerary = []
        itinerary.append({"day_range": f"Day 1-{f1}", "place": "Vilnius"})
        itinerary.append({"day_range": f"Day {f1}", "place": "Vilnius"})
        itinerary.append({"day_range": f"Day {f1}", "place": "Munich"})
        itinerary.append({"day_range": f"Day {f1}-{f2}", "place": "Munich"})
        itinerary.append({"day_range": f"Day {f2}", "place": "Munich"})
        itinerary.append({"day_range": f"Day {f2}", "place": "Mykonos"})
        itinerary.append({"day_range": f"Day {f2}-12", "place": "Mykonos"})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()