from z3 import *
import json

def main():
    s = Solver()
    cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    req = [7, 5, 4, 2]
    
    c1 = Int('c1')
    c2 = Int('c2')
    c3 = Int('c3')
    c4 = Int('c4')
    
    s.add(Distinct(c1, c2, c3, c4))
    for x in [c1, c2, c3, c4]:
        s.add(x >= 0, x < 4)
    
    def req_city(idx):
        return If(idx == 0, req[0],
               If(idx == 1, req[1],
               If(idx == 2, req[2], 
               req[3])))
    
    L1 = req_city(c1)
    L2 = req_city(c2)
    L3 = req_city(c3)
    L4 = req_city(c4)
    
    allowed_edges = [
        (0, 1), (1, 0),
        (0, 2), (2, 0),
        (0, 3), (3, 0),
        (1, 3), (3, 1),
        (2, 3), (3, 2)
    ]
    
    def edge(i, j):
        conditions = []
        for a, b in allowed_edges:
            conditions.append(And(i == a, j == b))
        return Or(conditions)
    
    s.add(edge(c1, c2))
    s.add(edge(c2, c3))
    s.add(edge(c3, c4))
    
    manchester_constraint = Or(
        And(c1 == 0, True),
        And(c2 == 0, L1 <= 7),
        And(c3 == 0, L1 + L2 <= 8),
        And(c4 == 0, L1 + L2 + L3 <= 9)
    )
    s.add(manchester_constraint)
    
    stuttgart_constraint = Or(
        And(c1 == 1, L1 >= 11),
        And(c2 == 1, And(L1 <= 15, L1 + L2 >= 12)),
        And(c3 == 1, And(L1 + L2 <= 16, L1 + L2 + L3 >= 13)),
        And(c4 == 1, True)
    )
    s.add(stuttgart_constraint)
    
    if s.check() == sat:
        m = s.model()
        c1_val = m.evaluate(c1).as_long()
        c2_val = m.evaluate(c2).as_long()
        c3_val = m.evaluate(c3).as_long()
        c4_val = m.evaluate(c4).as_long()
        
        city1 = cities[c1_val]
        city2 = cities[c2_val]
        city3 = cities[c3_val]
        city4 = cities[c4_val]
        
        req_dict = {city: req[i] for i, city in enumerate(cities)}
        L1_val = req_dict[city1]
        L2_val = req_dict[city2]
        L3_val = req_dict[city3]
        L4_val = req_dict[city4]
        
        e1 = L1_val
        e2 = e1 + L2_val - 1
        e3 = e1 + L2_val + L3_val - 2
        
        itinerary = []
        for d in range(1, 16):
            if d < e1:
                places = [city1]
            elif d == e1:
                places = [city1, city2]
            elif d < e2:
                places = [city2]
            elif d == e2:
                places = [city2, city3]
            elif d < e3:
                places = [city3]
            elif d == e3:
                places = [city3, city4]
            else:
                places = [city4]
            itinerary.append({"day": d, "place": places})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()