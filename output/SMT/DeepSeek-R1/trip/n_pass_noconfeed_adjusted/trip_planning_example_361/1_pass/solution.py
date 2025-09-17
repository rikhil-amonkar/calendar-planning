from z3 import *
import json

def main():
    # Initialize solver
    s = Solver()
    
    # City representations
    cities = {"Madrid": 0, "Paris": 1, "Bucharest": 2, "Seville": 3}
    city_names = {0: "Madrid", 1: "Paris", 2: "Bucharest", 3: "Seville"}
    
    # Stay variables: city, start day, end day for each of the 4 stays
    c0, c1, c2, c3 = Ints('c0 c1 c2 c3')
    s0, e0 = Ints('s0 e0')
    s1, e1 = Ints('s1 e1')
    s2, e2 = Ints('s2 e2')
    s3, e3 = Ints('s3 e3')
    
    # Fixed constraints
    s.add(s0 == 1, e3 == 15)
    s.add(e0 == 7, s3 == 14)  # From event constraints
    
    # Stay connectivity
    s.add(s1 == e0, s2 == e1, s3 == e2)
    
    # City assignments
    s.add(c0 == cities["Madrid"], c3 == cities["Bucharest"])
    s.add(Or(And(c1 == cities["Paris"], c2 == cities["Seville"]), 
             And(c1 == cities["Seville"], c2 == cities["Paris"])))
    
    # Stay duration constraints
    s.add(e0 - s0 + 1 == 7)  # Madrid
    s.add(e3 - s3 + 1 == 2)  # Bucharest
    s.add(Or(
        And(e1 - s1 + 1 == 6, e2 - s2 + 1 == 3),  # Paris then Seville
        And(e1 - s1 + 1 == 3, e2 - s2 + 1 == 6)   # Seville then Paris
    ))
    
    # Direct flight constraints
    flight_pairs = [
        (cities["Paris"], cities["Bucharest"]),
        (cities["Seville"], cities["Paris"]),
        (cities["Madrid"], cities["Bucharest"]),
        (cities["Madrid"], cities["Paris"]),
        (cities["Madrid"], cities["Seville"])
    ]
    
    def is_connected(city_a, city_b):
        constraints = []
        for a, b in flight_pairs:
            constraints.append(And(city_a == a, city_b == b))
            constraints.append(And(city_a == b, city_b == a))
        return Or(constraints)
    
    s.add(is_connected(c0, c1))
    s.add(is_connected(c1, c2))
    s.add(is_connected(c2, c3))
    
    # Check feasibility
    if s.check() == sat:
        m = s.model()
        # Extract values
        stays = [
            (m.evaluate(c0).as_long(), m.evaluate(s0).as_long(), m.evaluate(e0).as_long()),
            (m.evaluate(c1).as_long(), m.evaluate(s1).as_long(), m.evaluate(e1).as_long()),
            (m.evaluate(c2).as_long(), m.evaluate(s2).as_long(), m.evaluate(e2).as_long()),
            (m.evaluate(c3).as_long(), m.evaluate(s3).as_long(), m.evaluate(e3).as_long())
        ]
        
        # Build itinerary
        itinerary = []
        for city_code, start, end in stays:
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city_names[city_code]})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()