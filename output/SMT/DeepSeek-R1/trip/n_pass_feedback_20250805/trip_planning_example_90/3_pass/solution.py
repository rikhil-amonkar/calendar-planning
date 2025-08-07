from z3 import *
import json

def main():
    s = Solver()
    
    A = Int('A')  # Starting city: 0 for Naples, 2 for Vilnius
    d1 = Int('d1')  # First flight day (leave first city for Vienna)
    d2 = Int('d2')  # Second flight day (leave Vienna for third city)
    
    s.add(Or(A == 0, A == 2))
    s.add(d1 >= 1, d1 < d2, d2 <= 17)
    
    naples_days = If(A == 0, d1, 17 - d2 + 1)
    vienna_days = d2 - d1 + 1
    vilnius_days = If(A == 0, 17 - d2 + 1, d1)
    
    s.add(naples_days == 5)
    s.add(vienna_days == 7)
    s.add(vilnius_days == 7)
    
    s.add(If(A == 2, d2 <= 5, True))
    
    if s.check() == sat:
        m = s.model()
        A_val = m[A].as_long()
        d1_val = m[d1].as_long()
        d2_val = m[d2].as_long()
        
        if A_val == 0:
            segments = [
                {'day_range': f"Day 1-{d1_val}", 'place': 'Naples'},
                {'day_range': f"Day {d1_val}-{d2_val}", 'place': 'Vienna'},
                {'day_range': f"Day {d2_val}-17", 'place': 'Vilnius'}
            ]
        else:
            segments = [
                {'day_range': f"Day 1-{d1_val}", 'place': 'Vilnius'},
                {'day_range': f"Day {d1_val}-{d2_val}", 'place': 'Vienna'},
                {'day_range': f"Day {d2_val}-17", 'place': 'Naples'}
            ]
        
        result = {"itinerary": segments}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()