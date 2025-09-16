from z3 import *
import json

def main():
    # Define city mapping
    city_names = {0: "Manchester", 1: "Stuttgart", 2: "Madrid", 3: "Vienna"}
    
    # Define direct flight edges
    edges = [(0, 1), (0, 2), (0, 3), (1, 3), (2, 3)]
    
    # Initialize Z3 variables
    c1, c2, c3, c4 = Ints('c1 c2 c3 c4')
    e1, e2, e3 = Ints('e1 e2 e3')
    
    s = Solver()
    
    # City indices must be 0 to 3 and distinct
    s.add([And(c >= 0, c <= 3) for c in [c1, c2, c3, c4]])
    s.add(Distinct(c1, c2, c3, c4))
    
    # End day constraints: 1 <= e1 < e2 < e3 <= 15
    s.add(e1 >= 1, e1 <= 15)
    s.add(e2 > e1, e2 <= 15)
    s.add(e3 > e2, e3 <= 15)
    
    # Flight constraints between consecutive segments
    flight_constr = lambda a, b: Or([Or(And(a == i, b == j), And(a == j, b == i)) for (i, j) in edges])
    s.add(flight_constr(c1, c2))
    s.add(flight_constr(c2, c3))
    s.add(flight_constr(c3, c4))
    
    # Days in each city
    days_city = lambda city: If(c1 == city, e1,
                                If(c2 == city, e2 - e1 + 1,
                                  If(c3 == city, e3 - e2 + 1,
                                    If(c4 == city, 16 - e3, 0))))
    s.add(days_city(0) == 7)  # Manchester
    s.add(days_city(1) == 5)  # Stuttgart
    s.add(days_city(2) == 4)  # Madrid
    s.add(days_city(3) == 2)  # Vienna
    
    # Event constraints
    # Manchester must have at least one day in [1,7]
    s.add(Or(
        c1 == 0,
        And(c2 == 0, e1 <= 7),
        And(c3 == 0, e2 <= 7),
        And(c4 == 0, e3 <= 7)
    ))
    # Stuttgart must have at least one day in [11,15]
    s.add(Or(
        And(c1 == 1, e1 >= 11),
        And(c2 == 1, e2 >= 11),
        And(c3 == 1, e3 >= 11),
        c4 == 1
    ))
    # Additional constraint: Must be in Stuttgart on day 15
    s.add(Or(
        And(c1 == 1, e1 == 15),
        And(c2 == 1, e2 == 15),
        And(c3 == 1, e3 == 15),
        c4 == 1
    ))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        c1_val = m[c1].as_long()
        c2_val = m[c2].as_long()
        c3_val = m[c3].as_long()
        c4_val = m[c4].as_long()
        e1_val = m[e1].as_long()
        e2_val = m[e2].as_long()
        e3_val = m[e3].as_long()
        
        # Generate itinerary
        itinerary = []
        for d in range(1, 16):
            if d < e1_val:
                itinerary.append({"day": d, "place": city_names[c1_val]})
            elif d == e1_val:
                itinerary.append({"day": d, "place": city_names[c1_val]})
                itinerary.append({"day": d, "place": city_names[c2_val]})
            elif d < e2_val:
                itinerary.append({"day": d, "place": city_names[c2_val]})
            elif d == e2_val:
                itinerary.append({"day": d, "place": city_names[c2_val]})
                itinerary.append({"day": d, "place": city_names[c3_val]})
            elif d < e3_val:
                itinerary.append({"day": d, "place": city_names[c3_val]})
            elif d == e3_val:
                itinerary.append({"day": d, "place": city_names[c3_val]})
                itinerary.append({"day": d, "place": city_names[c4_val]})
            else:  # d > e3_val
                itinerary.append({"day": d, "place": city_names[c4_val]})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()