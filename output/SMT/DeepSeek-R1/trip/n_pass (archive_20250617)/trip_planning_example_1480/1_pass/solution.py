from z3 import *

def main():
    s = Solver()

    # City indices
    cities = {
        'Geneva': 0,
        'Venice': 1,
        'Vienna': 2,
        'Vilnius': 3,
        'Riga': 4,
        'Brussels': 5,
        'Munich': 6,
        'Reykjavik': 7,
        'Madrid': 8,
        'Istanbul': 9
    }
    
    city_names = {v: k for k, v in cities.items()}
    
    days_arr = [4, 5, 4, 4, 2, 2, 5, 2, 4, 4]  # days for cities 0 to 9
    
    edges = set([
        (2,6), (5,9), (2,3), (6,8), (1,5), (4,5), (0,9), (6,7), (2,9), (4,9), 
        (2,7), (1,6), (1,8), (3,9), (1,2), (1,9), (7,8), (4,6), (6,9), (5,7), 
        (3,5), (3,6), (2,8), (2,4), (0,2), (0,5), (5,8), (2,5), (0,8), (5,6), 
        (8,9), (0,6), (3,4)
    ])
    
    seq = [Int(f'seq_{i}') for i in range(10)]
    starts = [Int(f'starts_{i}') for i in range(10)]
    
    # Constraint: sequence is a permutation of 0..9
    s.add(Distinct(seq))
    for i in range(10):
        s.add(seq[i] >= 0, seq[i] <= 9)
    
    # Last city must be Brussels (index 5)
    s.add(seq[9] == 5)
    
    # Start of the first city is day 1
    s.add(starts[0] == 1)
    
    # Define start days for the rest of the cities
    for i in range(1, 10):
        prev_city = seq[i-1]
        days_val = If(prev_city == 0, 4,
                  If(prev_city == 1, 5,
                  If(prev_city == 2, 4,
                  If(prev_city == 3, 4,
                  If(prev_city == 4, 2,
                  If(prev_city == 5, 2,
                  If(prev_city == 6, 5,
                  If(prev_city == 7, 2,
                  If(prev_city == 8, 4,
                  If(prev_city == 9, 4, 0)))))))))
        s.add(starts[i] == starts[i-1] + (days_val - 1))
    
    # Define start day for each city (by index)
    s_city = [Int(f's_city_{i}') for i in range(10)]
    for i in range(10):
        s.add(s_city[i] == Sum([If(seq[j] == i, starts[j], 0) for j in range(10)]))
    
    # Event constraints
    # Geneva (0) must start by day 4
    s.add(s_city[0] <= 4)
    # Venice (1) must start between day 4 and 11 (inclusive)
    s.add(s_city[1] >= 4, s_city[1] <= 11)
    # Vilnius (3) must start between day 17 and 23 (inclusive)
    s.add(s_city[3] >= 17, s_city[3] <= 23)
    
    # Flight constraints between consecutive cities
    for i in range(9):
        c1 = seq[i]
        c2 = seq[i+1]
        conds = []
        for (a, b) in edges:
            conds.append(Or(And(c1 == a, c2 == b), And(c1 == b, c2 == a)))
        s.add(Or(conds))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(10)]
        starts_val = [m.evaluate(starts[i]).as_long() for i in range(10)]
        s_city_val = [m.evaluate(s_city[i]).as_long() for i in range(10)]
        
        print("Trip Plan:")
        for pos in range(10):
            city_idx = seq_val[pos]
            start_day = starts_val[pos]
            end_day = start_day + days_arr[city_idx] - 1
            print(f"From day {start_day} to {end_day}: {city_names[city_idx]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()