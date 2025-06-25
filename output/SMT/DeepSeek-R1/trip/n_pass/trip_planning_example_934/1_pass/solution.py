from z3 import *

def main():
    cities = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Budapest', 'Riga', 'Valencia']
    n = 7
    days_req_list = [5, 2, 3, 5, 2, 4, 2]
    
    adj = [
        [0,1,0,1,1,1,1],
        [1,0,1,1,1,1,1],
        [0,1,0,1,0,0,0],
        [1,1,1,0,1,0,1],
        [1,1,0,1,0,0,0],
        [1,1,0,0,0,0,0],
        [1,1,0,1,0,0,0]
    ]
    
    Y = [Int(f'Y{i}') for i in range(7)]
    s = Solver()
    
    for i in range(7):
        s.add(Y[i] >= 0, Y[i] < 7)
    s.add(Distinct(Y))
    
    a = [Int(f'a{i}') for i in range(7)]
    for i in range(7):
        conds = []
        for cidx in range(7):
            conds.append(And(Y[i] == cidx, a[i] == days_req_list[cidx]))
        s.add(Or(conds))
    
    start = [Int(f'start{i}') for i in range(7)]
    end = [Int(f'end{i}') for i in range(7)]
    
    s.add(start[0] == 1)
    s.add(end[0] == start[0] + a[0] - 1)
    for i in range(1, 7):
        s.add(start[i] == end[i-1])
        s.add(end[i] == start[i] + a[i] - 1)
    
    for i in range(6):
        conds = []
        for u in range(7):
            for v in range(7):
                if adj[u][v] == 1:
                    conds.append(And(Y[i] == u, Y[i+1] == v))
        s.add(Or(conds))
    
    brussels_conds = []
    for i in range(7):
        brussels_conds.append(And(Y[i] == 0, start[i] <= 11, end[i] >= 7))
    s.add(Or(brussels_conds))
    
    riga_conds = []
    for i in range(7):
        riga_conds.append(And(Y[i] == 5, start[i] <= 7, end[i] >= 4))
    s.add(Or(riga_conds))
    
    budapest_conds = []
    for i in range(7):
        budapest_conds.append(And(Y[i] == 4, end[i] >= 16))
    s.add(Or(budapest_conds))
    
    if s.check() == sat:
        m = s.model()
        order = [m.evaluate(Y[i]).as_long() for i in range(7)]
        city_order = [cities[idx] for idx in order]
        s_val = [m.evaluate(start[i]).as_long() for i in range(7)]
        e_val = [m.evaluate(end[i]).as_long() for i in range(7)]
        
        itinerary = []
        for i in range(7):
            s_i = s_val[i]
            e_i = e_val[i]
            if s_i == e_i:
                day_range = f"Day {s_i}"
            else:
                day_range = f"Day {s_i}-{e_i}"
            itinerary.append({"day_range": day_range, "place": city_order[i]})
            if i < 6:
                itinerary.append({"day_range": f"Day {e_i}", "place": city_order[i]})
                itinerary.append({"day_range": f"Day {e_i}", "place": city_order[i+1]})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()