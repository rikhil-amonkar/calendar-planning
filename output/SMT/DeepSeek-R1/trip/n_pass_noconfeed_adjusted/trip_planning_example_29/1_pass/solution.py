import json
from z3 import *

def main():
    # Define the variables for flight days
    T1 = Int('T1')  # First flight day (from Dubrovnik to Frankfurt)
    T2 = Int('T2')  # Second flight day (from Frankfurt to Krakow)
    
    s = Solver()
    # Constraints: T1 and T2 must be between 1 and 10, and T1 < T2
    s.add(T1 >= 1, T1 <= 10)
    s.add(T2 >= 1, T2 <= 10)
    s.add(T1 < T2)
    
    # City day constraints
    s.add(T1 == 7)  # Days in Dubrovnik
    s.add(T2 - T1 + 1 == 3)  # Days in Frankfurt
    s.add(10 - T2 + 1 == 2)  # Days in Krakow
    
    if s.check() == sat:
        m = s.model()
        t1_val = m[T1].as_long()
        t2_val = m[T2].as_long()
        
        itinerary = [
            {"day_range": f"Day 1-{t1_val}", "place": "Dubrovnik"},
            {"day_range": f"Day {t1_val}-{t2_val}", "place": "Frankfurt"},
            {"day_range": f"Day {t2_val}-10", "place": "Krakow"}
        ]
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No valid itinerary found')

if __name__ == '__main__':
    main()