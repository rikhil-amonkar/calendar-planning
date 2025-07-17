from z3 import *

def main():
    # Travel time matrix (10x10: indices 0 to 9)
    travel = [
        [0, 11, 19, 12, 18, 23, 17, 10, 15, 7],
        [12, 0, 15, 16, 14, 22, 19, 20, 24, 17],
        [18, 14, 0, 15, 15, 15, 18, 20, 27, 22],
        [11, 15, 12, 0, 22, 13, 6, 12, 21, 15],
        [19, 13, 18, 23, 0, 25, 27, 25, 23, 22],
        [22, 22, 13, 12, 26, 0, 9, 18, 27, 25],
        [16, 20, 16, 7, 27, 10, 0, 11, 19, 18],
        [10, 20, 21, 10, 27, 18, 9, 0, 11, 9],
        [15, 25, 30, 21, 22, 29, 21, 12, 0, 11],
        [7, 17, 22, 16, 23, 24, 16, 7, 10, 0]
    ]
    
    # Friend data: location index, window start (minutes from 9:00 AM), window end, min_time
    window_start = [0] * 10
    window_end = [0] * 10
    min_time_arr = [0] * 10
    
    # Elizabeth (location 1)
    window_start[1] = 90    # 10:30 AM
    window_end[1] = 660     # 8:00 PM
    min_time_arr[1] = 90
    
    # David (location 2)
    window_start[2] = 375   # 3:15 PM
    window_end[2] = 600     # 7:00 PM
    min_time_arr[2] = 45
    
    # Sandra (location 3)
    window_start[3] = 0     # 9:00 AM (adjusted)
    window_end[3] = 660     # 8:00 PM
    min_time_arr[3] = 120
    
    # Thomas (location 4)
    window_start[4] = 630   # 7:30 PM
    window_end[4] = 690     # 8:30 PM
    min_time_arr[4] = 30
    
    # Robert (location 5)
    window_start[5] = 60    # 10:00 AM
    window_end[5] = 360     # 3:00 PM
    min_time_arr[5] = 15
    
    # Kenneth (location 6)
    window_start[6] = 105   # 10:45 AM
    window_end[6] = 240     # 1:00 PM
    min_time_arr[6] = 45
    
    # Melissa (location 7)
    window_start[7] = 555   # 6:15 PM
    window_end[7] = 660     # 8:00 PM
    min_time_arr[7] = 15
    
    # Kimberly (location 8)
    window_start[8] = 75    # 10:15 AM
    window_end[8] = 555     # 6:15 PM
    min_time_arr[8] = 105
    
    # Amanda (location 9)
    window_start[9] = 0     # 9:00 AM (adjusted)
    window_end[9] = 585     # 6:45 PM
    min_time_arr[9] = 15
    
    # Initialize Z3 variables
    next_vars = [Int('next_%d' % i) for i in range(0, 10)]
    meet_vars = [Bool('meet_%d' % i) for i in range(1, 10)]
    start_vars = [Int('start_%d' % i) for i in range(1, 10)]
    
    s = Optimize()
    
    # Constraint 1: next_0 in [1..9,10]
    s.add(Or([next_vars[0] == i for i in range(1, 11)]))
    
    # Constraint 2: for i in 1..9, next_i in [1..9,10] and next_i != i
    for i in range(1, 10):
        s.add(Or([next_vars[i] == j for j in range(1, 11)]))
        s.add(next_vars[i] != i)
    
    # Constraint 3: for each friend i (location i, i in 1..9), meet_i is true iff exactly one j in 0..9 has next_j == i
    for idx, i in enumerate(range(1, 10)):
        meet_i = meet_vars[idx]
        cond = Sum([If(next_vars[j] == i, 1, 0) for j in range(0, 10)]) == 1
        s.add(meet_i == cond)
    
    # Constraint 4: exactly one j in 0..9 has next_j == 10
    s.add(Sum([If(next_vars[j] == 10, 1, 0) for j in range(0, 10)]) == 1)
    
    # Constraint 8: for j in 1..9, if next_j == i (for any i in 1..10), then meet_j must be true
    for j in range(1, 10):
        for i_val in range(1, 11):
            s.add(Implies(next_vars[j] == i_val, meet_vars[j-1]))
    
    # Define T_j: T0 = 0, and for j in 1..9, T_j = if meet_j then start_j + min_time_j else 0
    T = [0] * 10
    T[0] = 0
    for j in range(1, 10):
        T[j] = If(meet_vars[j-1], start_vars[j-1] + min_time_arr[j], 0)
    
    # Constraint 5: for each friend i (location i, i in 1..9) and for each j in 0..9, 
    # if next_j == i then start_i >= T_j + travel[j][i]
    for i_loc in range(1, 10):
        idx_i = i_loc - 1
        for j_loc in range(0, 10):
            s.add(Implies(next_vars[j_loc] == i_loc, 
                          start_vars[idx_i] >= T[j_loc] + travel[j_loc][i_loc]))
    
    # Constraint 6: for each friend i, window constraints
    for i_loc in range(1, 10):
        idx_i = i_loc - 1
        s.add(Implies(meet_vars[idx_i], start_vars[idx_i] >= window_start[i_loc]))
        s.add(Implies(meet_vars[idx_i], start_vars[idx_i] + min_time_arr[i_loc] <= window_end[i_loc]))
        s.add(start_vars[idx_i] >= 0)
        s.add(start_vars[idx_i] <= 690)
    
    # Constraint 7: for each j in 0..9, if next_j == 10, then T_j <= 690
    for j_loc in range(0, 10):
        s.add(Implies(next_vars[j_loc] == 10, T[j_loc] <= 690))
    
    # Objective: maximize the number of friends met
    objective = Sum([If(meet_vars[i], 1, 0) for i in range(0, 9)])
    s.maximize(objective)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        num_met = 0
        for i in range(0, 9):
            if m.evaluate(meet_vars[i]):
                num_met += 1
        print(f"Total friends met: {num_met}")
        for i in range(0, 10):
            next_val = m.evaluate(next_vars[i])
            print(f"next_{i} = {next_val}")
        for i in range(1, 10):
            idx = i-1
            if m.evaluate(meet_vars[idx]):
                start_val = m.evaluate(start_vars[idx])
                minutes = start_val.as_long()
                hours = 9 + minutes // 60
                mins = minutes % 60
                print(f"Meet friend at location {i} starting at {hours}:{mins:02d}, duration {min_time_arr[i]} minutes")
            else:
                print(f"Do not meet friend at location {i}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()