from z3 import *

def main():
    s = Solver()
    days = 14
    cities = {0: 'Split', 1: 'Vilnius', 2: 'Santorini', 3: 'Madrid'}
    
    start = [Int('start_%d' % (i+1)) for i in range(days)]
    travel = [Bool('travel_%d' % (i+1)) for i in range(days)]
    dest = [Int('dest_%d' % (i+1)) for i in range(days)]
    
    for i in range(days):
        s.add(start[i] >= 0, start[i] <= 3)
        s.add(dest[i] >= 0, dest[i] <= 3)
    
    for i in range(days-1):
        s.add(If(travel[i], start[i+1] == dest[i], start[i+1] == start[i]))
    
    allowed_pairs = [
        (0, 1), (0, 3),
        (1, 0),
        (3, 0), (3, 2),
        (2, 3)
    ]
    
    for i in range(days):
        constraints = []
        for pair in allowed_pairs:
            constraints.append(And(start[i] == pair[0], dest[i] == pair[1]))
        s.add(Implies(travel[i], Or(constraints)))
    
    total_travel = Sum([If(travel[i], 1, 0) for i in range(days)])
    s.add(total_travel == 3)
    
    non_travel_days = [0]*4
    travel_days = [0]*4
    total_days = [0]*4
    
    for c in range(4):
        non_travel_list = [If(And(Not(travel[i]), start[i] == c), 1, 0) for i in range(days)]
        non_travel_days[c] = Sum(non_travel_list)
        
        travel_list = [If(And(travel[i], Or(start[i] == c, dest[i] == c)), 1, 0) for i in range(days)]
        travel_days[c] = Sum(travel_list)
        
        total_days[c] = non_travel_days[c] + travel_days[c]
    
    s.add(total_days[0] == 5)
    s.add(total_days[1] == 4)
    s.add(total_days[2] == 2)
    s.add(total_days[3] == 6)
    
    s.add(start[0] == 1)
    
    for i in range(12):
        s.add(start[i] != 2)
        s.add(Implies(travel[i], dest[i] != 2))
    
    s.add(Or(start[12] == 2, And(travel[12], dest[12] == 2)))
    s.add(start[13] == 2)
    s.add(Not(travel[13]))
    
    if s.check() == sat:
        m = s.model()
        start_vals = [m.evaluate(start[i]).as_long() for i in range(days)]
        travel_vals = [is_true(m.evaluate(travel[i])) for i in range(days)]
        dest_vals = [m.evaluate(dest[i]).as_long() for i in range(days)]
        
        print("Day-by-Day Plan:")
        for i in range(days):
            if travel_vals[i]:
                dep_city = cities[start_vals[i]]
                arr_city = cities[dest_vals[i]]
                print(f"Day {i+1}: [{dep_city}, {arr_city}]")
            else:
                print(f"Day {i+1}: [{cities[start_vals[i]]}]")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()