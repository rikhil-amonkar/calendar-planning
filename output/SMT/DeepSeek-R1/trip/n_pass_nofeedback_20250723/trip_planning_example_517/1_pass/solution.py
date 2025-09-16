from z3 import *
import json

def main():
    cities = ["Dubrovnik", "Warsaw", "Stuttgart", "Bucharest", "Copenhagen"]
    s = [Int(f's_{i}') for i in range(20)]
    solver = Solver()
    
    for i in range(20):
        solver.add(s[i] >= 0, s[i] < 5)
    
    direct_pairs = [("Warsaw", "Copenhagen"), 
                   ("Stuttgart", "Copenhagen"), 
                   ("Warsaw", "Stuttgart"), 
                   ("Bucharest", "Copenhagen"), 
                   ("Bucharest", "Warsaw"), 
                   ("Copenhagen", "Dubrovnik")]
    allowed_set = set()
    for (c1, c2) in direct_pairs:
        i1 = cities.index(c1)
        i2 = cities.index(c2)
        allowed_set.add((i1, i2))
        allowed_set.add((i2, i1))
    
    for i in range(19):
        a = s[i]
        b = s[i+1]
        constraints = []
        for (x, y) in allowed_set:
            constraints.append(And(a == x, b == y))
        solver.add(If(a != b, Or(constraints), True)
    
    total_days = [0] * 5
    for c in range(5):
        days_list = []
        for d in range(1, 20):
            cond = Or(s[d-1] == c, s[d] == c)
            days_list.append(If(cond, 1, 0))
        total_days[c] = Sum(days_list)
    
    solver.add(total_days[0] == 5)
    solver.add(total_days[1] == 2)
    solver.add(total_days[2] == 7)
    solver.add(total_days[3] == 6)
    solver.add(total_days[4] == 3)
    
    solver.add(Or(s[6] == 2, s[7] == 2))
    solver.add(Or(s[12] == 2, s[13] == 2))
    
    wedding_constraints = []
    for d in range(1, 7):
        wedding_constraints.append(Or(s[d-1] == 3, s[d] == 3))
    solver.add(Or(wedding_constraints))
    
    if solver.check() == sat:
        m = solver.model()
        s_vals = [m.evaluate(s[i]).as_long() for i in range(20)]
        
        itinerary = []
        for d in range(1, 20):
            idx1 = s_vals[d-1]
            idx2 = s_vals[d]
            c1 = cities[idx1]
            c2 = cities[idx2]
            if c1 == c2:
                places = [c1]
            else:
                places = sorted([c1, c2])
            itinerary.append({"day": d, "place": places})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()