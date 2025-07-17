from z3 import *
import json

def main():
    # Define city indices
    Porto, Stuttgart, Seville, Madrid = 0, 1, 2, 3
    city_names = {
        Porto: 'Porto',
        Stuttgart: 'Stuttgart',
        Seville: 'Seville',
        Madrid: 'Madrid'
    }
    
    # Required days per city
    req_days = {Porto: 3, Stuttgart: 7, Seville: 2, Madrid: 4}
    
    # Direct flights (undirected)
    direct_flights = [
        (Porto, Stuttgart), (Stuttgart, Porto),
        (Seville, Porto), (Porto, Seville),
        (Madrid, Porto), (Porto, Madrid),
        (Madrid, Seville), (Seville, Madrid)
    ]
    
    # Initialize solver
    s = Solver()
    
    # Stay variables
    s0, s1, s2, s3 = Ints('s0 s1 s2 s3')
    e1, e2, e3 = Ints('e1 e2 e3')
    
    # Fixed constraints
    s.add(s3 == Stuttgart)
    s.add(e3 == 7)
    s.add(e2 == 5)
    s.add(s2 == Porto)
    
    # Distinct cities for stays
    s.add(Distinct(s0, s1, s2, s3))
    s.add(s0 >= 0, s0 <= 3)
    s.add(s1 >= 0, s1 <= 3)
    s.add(s2 >= 0, s2 <= 3)
    s.add(s3 >= 0, s3 <= 3)
    
    # Days per stay constraints
    s.add(Or(
        And(s0 == Seville, e1 == 2),
        And(s0 == Madrid, e1 == 4)
    ))
    s.add(Or(
        And(s1 == Seville, (e2 - e1 + 1) == 2),
        And(s1 == Madrid, (e2 - e1 + 1) == 4)
    ))
    
    # Flight constraints
    s.add(Or([And(s0 == i, s1 == j) for (i, j) in direct_flights]))
    s.add(Or([And(s1 == i, s2 == j) for (i, j) in direct_flights]))
    s.add(Or([And(s2 == i, s3 == j) for (i, j) in direct_flights]))
    
    # Madrid constraint (must be between day 1 and 4)
    s.add(Or(
        s0 == Madrid,
        And(s1 == Madrid, e1 <= 4),
        And(s2 == Madrid, e2 <= 4)
    ))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        s0_val = m[s0].as_long()
        s1_val = m[s1].as_long()
        s2_val = m[s2].as_long()
        s3_val = m[s3].as_long()
        e1_val = m[e1].as_long()
        e2_val = m[e2].as_long()
        e3_val = m[e3].as_long()
        
        # Build itinerary
        itinerary = []
        itinerary.append({"day_range": f"Day 1-{e1_val}", "place": city_names[s0_val]})
        itinerary.append({"day_range": f"Day {e1_val}", "place": city_names[s0_val]})
        itinerary.append({"day_range": f"Day {e1_val}", "place": city_names[s1_val]})
        itinerary.append({"day_range": f"Day {e1_val}-{e2_val}", "place": city_names[s1_val]})
        itinerary.append({"day_range": f"Day {e2_val}", "place": city_names[s1_val]})
        itinerary.append({"day_range": f"Day {e2_val}", "place": city_names[s2_val]})
        itinerary.append({"day_range": f"Day {e2_val}-{e3_val}", "place": city_names[s2_val]})
        itinerary.append({"day_range": f"Day {e3_val}", "place": city_names[s2_val]})
        itinerary.append({"day_range": f"Day {e3_val}", "place": city_names[s3_val]})
        itinerary.append({"day_range": f"Day {e3_val}-13", "place": city_names[s3_val]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()