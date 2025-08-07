from z3 import *
import json

def main():
    s = Solver()
    
    A = Int('A')  # First city: 0 for Naples, 2 for Vilnius
    d1 = Int('d1')  # First flight day
    d2 = Int('d2')  # Second flight day

    # A must be either 0 (Naples) or 2 (Vilnius)
    s.add(Or(A == 0, A == 2))
    
    # Constraints for days in each city based on A
    s.add(If(A == 0, 
             And(d1 == 5, d2 == 11), 
             And(d1 == 7, d2 == 13)))
    
    # Constraint for Vienna: must be 7 days
    s.add(d2 - d1 + 1 == 7)
    
    # Constraint for Naples visit between day 1 and 5
    s.add(Or(A == 0, d2 <= 5))
    
    # Flight day constraints
    s.add(d1 >= 1, d2 <= 17, d1 < d2)
    
    if s.check() == sat:
        m = s.model()
        A_val = m[A].as_long()
        d1_val = m[d1].as_long()
        d2_val = m[d2].as_long()
        
        # Map city indices to names
        city_names = {0: "Naples", 1: "Vienna", 2: "Vilnius"}
        
        # Determine city sequence
        if A_val == 0:
            cities = [0, 1, 2]  # Naples, Vienna, Vilnius
        else:
            cities = [2, 1, 0]  # Vilnius, Vienna, Naples
        
        itinerary = []
        for day in range(1, 18):
            if day < d1_val:
                places = [city_names[cities[0]]]
            elif day == d1_val:
                places = [city_names[cities[0]], city_names[cities[1]]]
            elif day < d2_val:
                places = [city_names[cities[1]]]
            elif day == d2_val:
                places = [city_names[cities[1]], city_names[cities[2]]]
            else:  # day > d2_val
                places = [city_names[cities[2]]]
            itinerary.append({"day": day, "place": places})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()