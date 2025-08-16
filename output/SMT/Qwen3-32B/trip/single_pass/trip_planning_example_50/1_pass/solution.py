import json
from z3 import *

def main():
    city1, city2, city3 = Ints('city1 city2 city3')
    d1, d2, d3 = Ints('d1 d2 d3')
    s = Solver()
    
    # All cities are distinct
    s.add(Distinct(city1, city2, city3))
    
    # Allowed transitions between city1 and city2
    s.add(Or(
        And(city1 == 0, city2 == 1),
        And(city1 == 1, city2 == 0),
        And(city1 == 1, city2 == 2),
        And(city1 == 2, city2 == 1)
    ))
    
    # Allowed transitions between city2 and city3
    s.add(Or(
        And(city2 == 0, city3 == 1),
        And(city2 == 1, city3 == 0),
        And(city2 == 1, city3 == 2),
        And(city2 == 2, city3 == 1)
    ))
    
    # Duration constraints based on city
    s.add(Or(And(city1 == 0, d1 == 4), And(city1 == 1, d1 == 3), And(city1 == 2, d1 == 7)))
    s.add(Or(And(city2 == 0, d2 == 4), And(city2 == 1, d2 == 3), And(city2 == 2, d2 == 7)))
    s.add(Or(And(city3 == 0, d3 == 4), And(city3 == 1, d3 == 3), And(city3 == 2, d3 == 7)))
    
    # Sum of durations is 14
    s.add(d1 + d2 + d3 == 14)
    
    if s.check() == sat:
        model = s.model()
        c1 = model[city1].as_long()
        c2 = model[city2].as_long()
        c3 = model[city3].as_long()
        d1_val = model[d1].as_long()
        d2_val = model[d2].as_long()
        d3_val = model[d3].as_long()
        
        segment1_days = d1_val
        segment2_start = segment1_days
        segment2_end = segment1_days + d2_val - 1
        segment3_start = segment2_end
        segment3_end = segment3_start + d3_val - 1
        
        itinerary = []
        for day in range(1, 13):
            if day <= segment1_days:
                city_code = c1
            elif day <= segment2_end:
                city_code = c2
            else:
                city_code = c3
            city_name = ""
            if city_code == 0:
                city_name = "Vilnius"
            elif city_code == 1:
                city_name = "Munich"
            else:
                city_name = "Mykonos"
            itinerary.append({"day": day, "city": city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()