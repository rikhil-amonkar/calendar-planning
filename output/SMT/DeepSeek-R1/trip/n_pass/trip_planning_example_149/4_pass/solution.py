from z3 import *

def main():
    s = [Int('s%d' % i) for i in range(1, 11)]  # s[0] to s[9] for day1 to day10
    t = [Bool('t%d' % i) for i in range(1, 11)]  # t[0] to t[9] for day1 to day10
    
    solver = Solver()
    allowed_pairs = [(0, 1), (1, 0), (1, 2), (2, 1)]
    
    # Constrain travel between days 1-9
    for i in range(9):
        valid_travel = Or([And(s[i] == a, s[i+1] == b) for (a, b) in allowed_pairs])
        solver.add(If(t[i], valid_travel, s[i] == s[i+1]))
    
    # No travel allowed on day 10
    solver.add(t[9] == False)
    
    # City counts (Istanbul:0, London:1, Santorini:2)
    count0 = count1 = count2 = 0
    
    # Count days 1-9
    for i in range(9):
        count0 += If(s[i] == 0, 1, 0)
        count1 += If(s[i] == 1, 1, 0)
        count2 += If(s[i] == 2, 1, 0)
        
        # Add destination city if traveling
        count0 += If(And(t[i], s[i+1] == 0), 1, 0)
        count1 += If(And(t[i], s[i+1] == 1), 1, 0)
        count2 += If(And(t[i], s[i+1] == 2), 1, 0)
    
    # Count day 10 (no travel)
    count0 += If(s[9] == 0, 1, 0)
    count1 += If(s[9] == 1, 1, 0)
    count2 += If(s[9] == 2, 1, 0)
    
    solver.add(count0 == 3, count1 == 3, count2 == 6)
    
    # Conference constraints
    solver.add(Or(s[4] == 2, And(t[4], s[5] == 2)))  # Day 5 in Santorini
    solver.add(s[9] == 2)  # Day 10 in Santorini
    
    # Start in Istanbul
    solver.add(s[0] == 0)
    
    # Exactly 2 travel days (only allowed on days 1-9)
    total_travels = Sum([If(t[i], 1, 0) for i in range(9)])
    solver.add(total_travels == 2)
    
    # Cities must be valid
    for i in range(10):
        solver.add(Or(s[i] == 0, s[i] == 1, s[i] == 2))
    
    # Solve and print
    if solver.check() == sat:
        m = solver.model()
        s_val = [m.evaluate(s_i) for s_i in s]
        t_val = [m.evaluate(t_i) for t_i in t]
        
        cities = ["Istanbul", "London", "Santorini"]
        for i in range(10):
            city_idx = s_val[i].as_long()
            city = cities[city_idx]
            if t_val[i]:
                next_city = cities[s_val[i+1].as_long()] if i < 9 else ""
                print(f"Day {i+1}: Start in {city}, fly to {next_city} -> in {city} and {next_city}")
            else:
                print(f"Day {i+1}: Stay in {city}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()