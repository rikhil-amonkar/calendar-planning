from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define variables for end days of stays
    e_brussels = Int('e_brussels')
    e_barcelona = Int('e_barcelona')
    
    # Fixed start and end days
    s_brussels = 1
    s_split = e_barcelona
    e_split = 12
    
    # Constraints
    s.add(e_brussels >= s_brussels + 1)  # At least 2 days in Brussels
    s.add(e_brussels - s_brussels + 1 == 2)  # Exactly 2 days in Brussels
    s.add(e_barcelona - e_brussels + 1 == 7)  # 7 days in Barcelona including travel
    s.add(e_split - s_split + 1 == 5)  # 5 days in Split including travel
    s.add(e_brussels <= e_barcelona)  # Order constraints
    s.add(e_barcelona <= e_split)
    s.add(e_brussels >= 1, e_brussels <= 12)
    s.add(e_barcelona >= 1, e_barcelona <= 12)
    
    # Check feasibility
    if s.check() == sat:
        m = s.model()
        e_brussels_val = m[e_brussels].as_long()
        e_barcelona_val = m[e_barcelona].as_long()
        
        # Construct itinerary
        itinerary = [
            {"day_range": f"Day 1-{e_brussels_val}", "place": "Brussels"},
            {"day_range": f"Day {e_brussels_val}-{e_barcelona_val}", "place": "Barcelona"},
            {"day_range": f"Day {e_barcelona_val}-12", "place": "Split"}
        ]
        
        # Output as JSON
        import json
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()