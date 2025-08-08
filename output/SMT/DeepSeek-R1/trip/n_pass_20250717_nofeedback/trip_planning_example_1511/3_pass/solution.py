from z3 import *

def solve_trip_scheduling(n_activities, durations, min_gaps, total_days):
    n = n_activities
    s = Solver()
    
    # Activity sequence variables
    seq = [Int(f'seq_{i}') for i in range(n)]
    # Start and end time variables for each activity
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]
    
    # Activity sequence constraints
    s.add(Distinct(seq))
    for i in range(n):
        s.add(seq[i] >= 0, seq[i] < n)
    
    # First activity starts at day 1
    for i in range(n):
        s.add(Implies(seq[0] == i, start[i] == 1))
    
    # Last activity ends on total_days
    for i in range(n):
        s.add(Implies(seq[n-1] == i, end[i] == total_days))
    
    # Duration constraints
    for i in range(n):
        s.add(end[i] == start[i] + durations[i] - 1)
        s.add(start[i] >= 1, end[i] <= total_days)
    
    # Gap constraints for every pair of activities
    for i in range(n):
        for j in range(n):
            if i != j:
                # If activity i comes before j in the sequence
                cond_before = And(
                    seq[i] < seq[j],
                    start[j] >= end[i] + min_gaps[i][j] + 1
                )
                # If activity j comes before i in the sequence
                cond_after = And(
                    seq[j] < seq[i],
                    start[i] >= end[j] + min_gaps[j][i] + 1
                )
                s.add(Or(cond_before, cond_after))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(n)]
        start_val = [m.evaluate(start[i]).as_long() for i in range(n)]
        end_val = [m.evaluate(end[i]).as_long() for i in range(n)]
        return seq_val, start_val, end_val
    else:
        return None, None, None

# Example usage
n_activities = 4
durations = [3, 2, 2, 3]
min_gaps = [
    [0, 1, 1, 1],
    [1, 0, 1, 1],
    [1, 1, 0, 1],
    [1, 1, 1, 0]
]
total_days = 10

seq, start, end = solve_trip_scheduling(n_activities, durations, min_gaps, total_days)
if seq is not None:
    print("Activity Sequence:", seq)
    print("Start Times:", start)
    print("End Times:", end)
else:
    print("No valid schedule found.")