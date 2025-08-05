from z3 import *
import json

def main():
    d1 = Int('d1')
    d2 = Int('d2')
    s0 = Int('s0')
    s1 = Int('s1')
    s2 = Int('s2')
    
    solver = Solver()
    
    solver.add(d1 >= 1, d1 <= 10, d2 >= 1, d2 <= 10, d1 < d2)
    
    solver.add(Or(
        And(s0 == 0, s1 == 1, s2 == 2),
        And(s0 == 2, s1 == 1, s2 == 0)
    ))
    
    solver.add(If(s0 == 0, d1 == 2,
                 If(s0 == 1, d1 == 4,
                    d1 == 6)))
    
    solver.add(If(s1 == 0, d2 - d1 + 1 == 2,
                 If(s1 == 1, d2 - d1 + 1 == 4,
                    d2 - d1 + 1 == 6)))
    
    solver.add(If(s2 == 0, 10 - d2 + 1 == 2,
                 If(s2 == 1, 10 - d2 + 1 == 4,
                    10 - d2 + 1 == 6)))
    
    if solver.check() == sat:
        m = solver.model()
        d1_val = m[d1].as_long()
        d2_val = m[d2].as_long()
        s0_val = m[s0].as_long()
        s1_val = m[s1].as_long()
        s2_val = m[s2].as_long()
        
        city_map = {0: "Mykonos", 1: "Vienna", 2: "Venice"}
        
        itinerary_list = []
        for day in range(1, 11):
            if day < d1_val:
                place = city_map[s0_val]
            elif day == d1_val:
                place = city_map[s0_val] + " and " + city_map[s1_val]
            elif day < d2_val:
                place = city_map[s1_val]
            elif day == d2_val:
                place = city_map[s1_val] + " and " + city_map[s2_val]
            else:
                place = city_map[s2_val]
            itinerary_list.append({"day": day, "place": place})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()