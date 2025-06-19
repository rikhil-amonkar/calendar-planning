from z3 import *

def main():
    # Create the solver
    s = Solver()
    
    # Cities: Vienna=0, Stockholm=1, Nice=2, Split=3
    c1, c2, c3, c4 = Ints('c1 c2 c3 c4')
    F1, F2, F3 = Ints('F1 F2 F3')
    
    # Define the direct flight graph as a list of allowed edges
    edges = [(0,1), (0,2), (0,3),
             (1,0), (1,2), (1,3),
             (2,0), (2,1),
             (3,0), (3,1)]
    
    # Constraints
    s.add(c1 == 0)  # Start in Vienna
    s.add(F1 == 2)   # First flight day is day 2
    
    s.add(c4 == 3)   # End in Split
    s.add(F3 == 7)   # Last flight day is day 7
    
    # c1, c2, c3, c4 are distinct and in {0,1,2,3}
    s.add(Distinct(c1, c2, c3, c4))
    s.add(And(c1 >= 0, c1 <= 3))
    s.add(And(c2 >= 0, c2 <= 3))
    s.add(And(c3 >= 0, c3 <= 3))
    s.add(And(c4 >= 0, c4 <= 3))
    
    # F1, F2, F3 are days: F1=2, F2 in [3,6], F3=7
    s.add(F1 == 2)
    s.add(F2 >= 3, F2 <= 6)
    s.add(F3 == 7)
    s.add(F2 < F3)
    
    # Days for Nice (2) and Stockholm (1)
    # If Nice is in c2, then days = F2 - F1 = F2 - 2? Actually: F2 - F1 + 1 = F2 - 1
    # If Nice is in c3, then days = F3 - F2 + 1 = 7 - F2 + 1 = 8 - F2
    s.add(
        Or(
            And(c2 == 2, F2 == 3, c3 == 1),   # Nice in c2: F2-1=2 => F2=3; Stockholm in c3: 8-3=5
            And(c2 == 1, F2 == 6, c3 == 2)    # Stockholm in c2: F2-1=5 => F2=6; Nice in c3: 8-6=2
        )
    )
    
    # Flight connections
    # From c1 to c2
    s.add(Or([And(c1 == i, c2 == j) for (i, j) in edges if i != j]))  # Ensure different cities
    # From c2 to c3
    s.add(Or([And(c2 == i, c3 == j) for (i, j) in edges if i != j]))
    # From c3 to c4
    s.add(Or([And(c3 == i, c4 == j) for (i, j) in edges if i != j]))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        c1_val = m[c1].as_long()
        c2_val = m[c2].as_long()
        c3_val = m[c3].as_long()
        c4_val = m[c4].as_long()
        F1_val = m[F1].as_long()
        F2_val = m[F2].as_long()
        F3_val = m[F3].as_long()
        
        # Map city numbers to names
        city_names = {0: "Vienna", 1: "Stockholm", 2: "Nice", 3: "Split"}
        c1_name = city_names[c1_val]
        c2_name = city_names[c2_val]
        c3_name = city_names[c3_val]
        c4_name = city_names[c4_val]
        
        # Build itinerary
        itinerary = [
            {"day_range": "Day 1-{}".format(F1_val), "place": c1_name},
            {"day_range": "Day {}".format(F1_val), "place": c1_name},
            {"day_range": "Day {}".format(F1_val), "place": c2_name},
            {"day_range": "Day {}-{}".format(F1_val, F2_val), "place": c2_name},
            {"day_range": "Day {}".format(F2_val), "place": c2_name},
            {"day_range": "Day {}".format(F2_val), "place": c3_name},
            {"day_range": "Day {}-{}".format(F2_val, F3_val), "place": c3_name},
            {"day_range": "Day {}".format(F3_val), "place": c3_name},
            {"day_range": "Day {}".format(F3_val), "place": c4_name},
            {"day_range": "Day {}-9".format(F3_val), "place": c4_name}
        ]
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()