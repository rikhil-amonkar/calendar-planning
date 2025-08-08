from z3 import *

def solve_trip_scheduling(n_activities, durations, min_gaps, total_days):
    n = n_activities
    s = Solver()
    
    # Position of each activity: pos[i] = k means activity i is the k-th in sequence
    pos = [Int(f'pos_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]
    
    # Position constraints: distinct positions in [0, n-1]
    s.add(Distinct(pos))
    for i in range(n):
        s.add(pos[i] >= 0, pos[i] < n)
    
    # First activity starts at day 1
    for i in range(n):
        s.add(Implies(pos[i] == 0, start[i] == 1))
    
    # Last activity ends at total_days
    for i in range(n):
        s.add(Implies(pos[i] == n-1, end[i] == total_days))
    
    # Duration constraints
    for i in range(n):
        s.add(end[i] == start[i] + durations[i] - 1)
        s.add(start[i] >= 1, end[i] <= total_days)
    
    # Non-overlap for all activity pairs
    for i in range(n):
        for j in range(i+1, n):
            s.add(Or(end[i] <= start[j], end[j] <= start[i]))
    
    # Minimum gap constraints for consecutive activities
    for i in range(n):
        for j in range(n):
            if i != j:
                # If j is immediately after i
                s.add(Implies(pos[j] == pos[i] + 1, 
                              start[j] >= end[i] + min_gaps[i][j] + 1))
                # If i is immediately after j
                s.add(Implies(pos[i] == pos[j] + 1, 
                              start[i] >= end[j] + min_gaps[j][i] + 1))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        pos_val = [m.evaluate(pos[i]).as_long() for i in range(n)]
        start_val = [m.evaluate(start[i]).as_long() for i in range(n)]
        end_val = [m.evaluate(end[i]).as_long() for i in range(n)]
        
        # Reconstruct activity sequence from positions
        seq_val = [0] * n
        for idx in range(n):
            for i in range(n):
                if pos_val[i] == idx:
                    seq_val[idx] = i
        return seq_val, start_val, end_val
    else:
        return None, None, None

# Example usage with adjusted min_gaps to allow a solution
n_activities = 4
durations = [3, 2, 2, 3]
min_gaps = [
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0],
    [0, 0, 0, 0]
]
total_days = 10

seq, start, end = solve_trip_scheduling(n_activities, durations, min_gaps, total_days)
if seq is not None:
    print("Activity Sequence:", seq)
    print("Start Times:", start)
    print("End Times:", end)
else:
    print("No valid schedule found")