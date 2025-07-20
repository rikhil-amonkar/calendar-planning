from z3 import *

def main():
    # Define the flight day variables
    f1 = Int('f1')  # Flight day from Naples to Vienna
    f2 = Int('f2')  # Flight day from Vienna to Vilnius
    
    s = Solver()
    
    # Constraints
    s.add(f1 >= 1, f1 <= 17)
    s.add(f2 >= 1, f2 <= 17)
    s.add(f1 == 5)  # Must leave Naples on day 5 to satisfy the 5-day stay and relative visit
    s.add(f2 - f1 + 1 == 7)  # Stay in Vienna is 7 days
    s.add(17 - f2 + 1 == 7)  # Stay in Vilnius is 7 days
    
    if s.check() == sat:
        m = s.model()
        f1_val = m[f1].as_long()
        f2_val = m[f2].as_long()
        
        itinerary = [
            {"day_range": f"Day 1-{f1_val}", "place": "Naples"},
            {"day_range": f"Day {f1_val}", "place": "Naples"},
            {"day_range": f"Day {f1_val}", "place": "Vienna"},
            {"day_range": f"Day {f1_val}-{f2_val}", "place": "Vienna"},
            {"day_range": f"Day {f2_val}", "place": "Vienna"},
            {"day_range": f"Day {f2_val}", "place": "Vilnius"},
            {"day_range": f"Day {f2_val}-17", "place": "Vilnius"}
        ]
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No valid itinerary found.")

if __name__ == "__main__":
    main()