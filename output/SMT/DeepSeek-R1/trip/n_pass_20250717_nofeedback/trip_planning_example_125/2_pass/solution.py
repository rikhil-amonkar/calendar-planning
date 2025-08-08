from z3 import *
import json

def main():
    s0, s1, s2 = Ints('s0 s1 s2')
    a = Int('a')
    b = Int('b')
    
    solver = Solver()
    
    allowed_pairs = [(0,2), (2,0), (1,2), (2,1)]
    
    solver.add(s0 >= 0, s0 <= 2)
    solver.add(s1 >= 0, s1 <= 2)
    solver.add(s2 >= 0, s2 <= 2)
    solver.add(Distinct(s0, s1, s2))
    
    solver.add(a >= 1, a <= 14)
    solver.add(b >= a+1, b <= 15)
    
    solver.add(Or([And(s0 == x, s1 == y) for (x, y) in allowed_pairs]))
    solver.add(Or([And(s1 == x, s2 == y) for (x, y) in allowed_pairs]))
    
    solver.add(Or(
        And(s0 == 0, a == 6),
        And(s0 == 1, a == 7),
        And(s0 == 2, a == 4)
    ))
    
    solver.add(Or(
        And(s1 == 0, b - a + 1 == 6),
        And(s1 == 1, b - a + 1 == 7),
        And(s1 == 2, b - a + 1 == 4)
    ))
    
    solver.add(Or(
        And(s2 == 0, b == 10),
        And(s2 == 1, b == 9),
        And(s2 == 2, b == 12)
    ))
    
    solver.add(Or(
        s0 == 0,
        And(s1 == 0, a <= 6)
    ))
    
    if solver.check() == sat:
        model = solver.model()
        a_val = model[a].as_long()
        b_val = model[b].as_long()
        s0_val = model[s0].as_long()
        s1_val = model[s1].as_long()
        s2_val = model[s2].as_long()
        
        city_names = {
            0: "Stuttgart",
            1: "Seville",
            2: "Manchester"
        }
        
        itinerary = []
        for day in range(1, 16):
            if day < a_val:
                itinerary.append({"day": day, "city": city_names[s0_val]})
            elif day == a_val:
                itinerary.append({"day": day, "city": city_names[s0_val]})
                itinerary.append({"day": day, "city": city_names[s1_val]})
            elif day < b_val:
                itinerary.append({"day": day, "city": city_names[s1_val]})
            elif day == b_val:
                itinerary.append({"day": day, "city": city_names[s1_val]})
                itinerary.append({"day": day, "city": city_names[s2_val]})
            else:
                itinerary.append({"day": day, "city": city_names[s2_val]})
        
        result = {
            "itinerary": itinerary
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()