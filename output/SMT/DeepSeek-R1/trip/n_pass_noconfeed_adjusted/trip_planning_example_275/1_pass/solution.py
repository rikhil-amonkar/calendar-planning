from z3 import *
import json

def main():
    # Define the variables for travel days
    x0, x1, x2 = Ints('x0 x1 x2')
    s = Solver()
    
    # Add constraints based on the required days in each city
    s.add(x0 == 4)
    s.add(x1 - x0 + 1 == 5)
    s.add(x2 - x1 + 1 == 6)
    s.add(14 - x2 + 1 == 2)
    s.add(1 <= x0, x0 < x1, x1 < x2, x2 <= 14)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        x0_val = m[x0].as_long()
        x1_val = m[x1].as_long()
        x2_val = m[x2].as_long()
        
        # Build the itinerary
        itinerary = [
            {"day_range": f"Day 1-{x0_val}", "place": "Vilnius"},
            {"day_range": f"Day {x0_val}-{x1_val}", "place": "Split"},
            {"day_range": f"Day {x1_val}-{x2_val}", "place": "Madrid"},
            {"day_range": f"Day {x2_val}-14", "place": "Santorini"}
        ]
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()