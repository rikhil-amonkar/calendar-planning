from z3 import *
import json

def main():
    s = Solver()
    
    A = Int('A')  # Starting city: 0 for Naples, 2 for Vilnius
    d1 = Int('d1')  # First flight day (leave first city for Vienna)
    d2 = Int('d2')  # Second flight day (leave Vienna for third city)
    
    # A must be either 0 (Naples) or 2 (Vilnius)
    s.add(Or(A == 0, A == 2))
    # Flight days constraints: 1 <= d1 < d2 <= 17
    s.add(d1 >= 1, d1 < d2, d2 <= 17)
    
    # Days in each city based on starting city
    naples_days = If(A == 0, d1, 17 - d2 + 1)
    vienna_days = d2 - d1 + 1
    vilnius_days = If(A == 0, 17 - d2 + 1, d1)
    
    # Add constraints for the required days in each city
    s.add(naples_days == 5)
    s.add(vienna_days == 7)
    s.add(vilnius_days == 7)
    
    # Constraint: Naples visit must include at least one day between day 1 and 5
    # If starting in Vilnius (A=2), then the arrival day in Naples (d2) must be <=5
    s.add(If(A == 2, d2 <= 5, True))
    
    if s.check() == sat:
        m = s.model()
        A_val = m[A].as_long()
        d1_val = m[d1].as_long()
        d2_val = m[d2].as_long()
        
        # Determine city sequence based on starting city
        if A_val == 0:
            city0 = "Naples"
            city1 = "Vienna"
            city2 = "Vilnius"
        else:
            city0 = "Vilnius"
            city1 = "Vienna"
            city2 = "Naples"
        
        itinerary = []
        for day in range(1, 18):  # Days 1 to 17
            if day < d1_val:
                places = [city0]
            elif day == d1_val:
                places = [city0, city1]
            elif day < d2_val:
                places = [city1]
            elif day == d2_val:
                places = [city1, city2]
            else:  # day > d2_val
                places = [city2]
            itinerary.append({"day": day, "place": places})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()