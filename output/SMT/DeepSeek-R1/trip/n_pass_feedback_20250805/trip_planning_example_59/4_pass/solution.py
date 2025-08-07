from z3 import Solver, Int, Or, And, If, sat
import json

def main():
    cities = {0: "Bucharest", 1: "Lyon", 2: "Porto"}
    n_days = 16
    s = Solver()
    
    M = [Int(f'M_{i+1}') for i in range(n_days)]
    E = [Int(f'E_{i+1}') for i in range(n_days)]
    
    for i in range(n_days):
        s.add(And(M[i] >= 0, M[i] <= 2))
        s.add(And(E[i] >= 0, E[i] <= 2))
    
    for i in range(n_days - 1):
        s.add(E[i] == M[i+1])
    
    valid_flights = [(0, 1), (1, 0), (1, 2), (2, 1)]
    for i in range(n_days):
        s.add(If(M[i] != E[i],
                 Or([And(M[i] == a, E[i] == b) for (a, b) in valid_flights]),
                 True))
    
    b_days = 0
    l_days = 0
    p_days = 0
    for i in range(n_days):
        in_b = Or(M[i] == 0, E[i] == 0)
        in_l = Or(M[i] == 1, E[i] == 1)
        in_p = Or(M[i] == 2, E[i] == 2)
        b_days += If(in_b, 1, 0)
        l_days += If(in_l, 1, 0)
        p_days += If(in_p, 1, 0)
    
    s.add(b_days == 7)
    s.add(l_days == 7)
    s.add(p_days == 4)
    
    wedding_days = []
    for i in range(7):
        in_b = Or(M[i] == 0, E[i] == 0)
        wedding_days.append(in_b)
    s.add(Or(wedding_days))
    
    if s.check() == sat:
        model = s.model()
        M_vals = [model.evaluate(M[i]).as_long() for i in range(n_days)]
        
        segments = []
        start_index = 0
        current_city = M_vals[0]
        for i in range(1, n_days):
            if M_vals[i] != current_city:
                segments.append({
                    "day_range": f"Day {start_index+1}-{i}",
                    "place": cities[current_city]
                })
                start_index = i
                current_city = M_vals[i]
        segments.append({
            "day_range": f"Day {start_index+1}-{n_days}",
            "place": cities[current_city]
        })
        
        result = {"itinerary": segments}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()