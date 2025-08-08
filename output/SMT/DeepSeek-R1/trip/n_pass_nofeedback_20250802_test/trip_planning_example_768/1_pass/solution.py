import json
from z3 import *

def main():
    cities = ["Mykonos", "Nice", "London", "Copenhagen", "Oslo", "Tallinn"]
    required_days = [4, 3, 2, 3, 5, 4]
    allowed_edges = set([
        (0,1), (0,2),
        (1,2), (1,3), (1,4),
        (2,3), (2,4),
        (3,4), (3,5),
        (4,5)
    ])
    
    s = [Int(f's_{i}') for i in range(17)]
    solver = Solver()
    
    for i in range(17):
        solver.add(s[i] >= 0, s[i] <= 5)
    
    for i in range(16):
        edge_ok = Or([Or(And(s[i] == a, s[i+1] == b), And(s[i] == b, s[i+1] == a)) for (a, b) in allowed_edges])
        solver.add(Or(s[i] == s[i+1], edge_ok))
    
    for c in range(6):
        total = 0
        for i in range(16):
            total += If(Or(s[i] == c, s[i+1] == c), 1, 0)
        solver.add(total == required_days[c])
    
    solver.add(Or(s[13] == 1, s[14] == 1))
    solver.add(Or(s[15] == 1, s[16] == 1))
    
    oslo_constraints = []
    for j in range(9, 14):
        oslo_constraints.append(Or(s[j] == 4, s[j+1] == 4))
    solver.add(Or(oslo_constraints))
    
    if solver.check() == sat:
        model = solver.model()
        s_val = [model.evaluate(s[i]).as_long() for i in range(17)]
        
        itinerary = []
        for i in range(16):
            start_city = cities[s_val[i]]
            end_city = cities[s_val[i+1]]
            if s_val[i] == s_val[i+1]:
                place_str = start_city
            else:
                place_str = start_city + " and " + end_city
            itinerary.append({"day": i+1, "place": place_str})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()