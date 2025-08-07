from z3 import *
import json

def main():
    a = Int('a')  # Flight day from Split to London
    b = Int('b')  # Flight day from London to Santorini
    
    s = Solver()
    
    # Constraints
    s.add(a >= 1, a <= 18)
    s.add(b >= 1, b <= 18)
    s.add(a < b)  # Flight from Split to London must occur before flight to Santorini
    
    # Split stay: days 1 to a (inclusive) -> length = a
    s.add(a == 6)  # Split must be 6 days
    
    # London stay: days a to b (inclusive) -> length = b - a + 1
    s.add(b - a == 6)  # London stay must be 7 days? b - a + 1 = 7 => b - a = 6
    
    # Santorini stay: days b to 18 (inclusive) -> length = 18 - b + 1
    s.add(18 - b + 1 == 7)  # Santorini stay must be 7 days
    
    # Conference constraints: must be in Santorini on day 12 and 18
    # Since Santorini starts on day b, we require b <= 12 and 18 is included
    s.add(b <= 12)
    
    if s.check() == sat:
        m = s.model()
        a_val = m[a].as_long()
        b_val = m[b].as_long()
        
        itinerary = [
            {"day_range": f"Day 1-{a_val}", "place": "Split"},
            {"day_range": f"Day {a_val}-{b_val}", "place": "London"},
            {"day_range": f"Day {b_val}-18", "place": "Santorini"}
        ]
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()