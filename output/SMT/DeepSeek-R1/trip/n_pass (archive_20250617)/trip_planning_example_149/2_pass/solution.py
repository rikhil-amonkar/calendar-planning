from z3 import *

def main():
    s = [Int('s%d' % (i+1)) for i in range(10)]
    t = [Bool('t%d' % (i+1)) for i in range(10)]
    d10 = Int('d10')
    
    solver = Solver()
    allowed_pairs = [(0, 1), (1, 0), (1, 2), (2, 1)]
    
    for i in range(9):
        cons = Or([And(s[i] == a, s[i+1] == b) for (a, b) in allowed_pairs])
        solver.add(If(t[i], cons, s[i] == s[i+1]))
    
    cons10 = Or([And(s[9] == a, d10 == b) for (a, b) in allowed_pairs])
    solver.add(If(t[9], cons10, True))
    solver.add(Or(d10 == 0, d10 == 1, d10 == 2))
    
    count0 = count1 = count2 = 0
    for i in range(9):
        count0 += If(s[i] == 0, 1, 0)
        count1 += If(s[i] == 1, 1, 0)
        count2 += If(s[i] == 2, 1, 0)
        count0 += If(And(t[i], s[i+1] == 0), 1, 0)
        count1 += If(And(t[i], s[i+1] == 1), 1, 0)
        count2 += If(And(t[i], s[i+1] == 2), 1, 0)
    
    count0 += If(s[9] == 0, 1, 0)
    count1 += If(s[9] == 1, 1, 0)
    count2 += If(s[9] == 2, 1, 0)
    count0 += If(And(t[9], d10 == 0), 1, 0)
    count1 += If(And(t[9], d10 == 1), 1, 0)
    count2 += If(And(t[9], d10 == 2), 1, 0)
    
    solver.add(count0 == 3, count1 == 3, count2 == 6)
    solver.add(Or(s[4] == 2, And(t[4], s[5] == 2)))
    solver.add(Or(s[9] == 2, And(t[9], d10 == 2)))
    
    for i in range(10):
        solver.add(Or(s[i] == 0, s[i] == 1, s[i] == 2))
    
    total_travels = Sum([If(t_i, 1, 0) for t_i in t])
    solver.add(total_travels == 2)
    
    if solver.check() == sat:
        m = solver.model()
        s_val = [m.evaluate(s_i) for s_i in s]
        t_val = [m.evaluate(t_i) for t_i in t]
        d10_val = m.evaluate(d10)
        
        cities = ["Istanbul", "London", "Santorini"]
        for i in range(10):
            city_idx = s_val[i].as_long()
            start_city = cities[city_idx]
            if t_val[i]:
                if i < 9:
                    dest_city = cities[s_val[i+1].as_long()]
                else:
                    dest_city = cities[d10_val.as_long()]
                print(f"Day {i+1}: Start in {start_city}, fly to {dest_city} -> in {start_city} and {dest_city}")
            else:
                print(f"Day {i+1}: Stay in {start_city}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()