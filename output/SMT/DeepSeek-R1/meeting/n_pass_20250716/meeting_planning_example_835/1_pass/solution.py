from z3 import *

def main():
    # Travel time matrix: 10x10 (indices 0 to 9)
    # 0: Pacific Heights, 1: Golden Gate Park, 2: The Castro, 3: Bayview, 4: Marina District,
    # 5: Union Square, 6: Sunset District, 7: Alamo Square, 8: Financial District, 9: Mission District
    T = [
        [0, 15, 16, 22, 6, 12, 21, 10, 13, 15],
        [16, 0, 13, 23, 16, 22, 10, 9, 26, 17],
        [16, 11, 0, 19, 21, 19, 17, 8, 21, 7],
        [23, 22, 19, 0, 27, 18, 23, 16, 19, 13],
        [7, 18, 22, 27, 0, 16, 19, 15, 17, 20],
        [15, 22, 17, 15, 18, 0, 27, 15, 9, 14],
        [21, 11, 17, 22, 21, 30, 0, 17, 30, 25],
        [10, 9, 8, 16, 15, 14, 16, 0, 17, 10],
        [13, 23, 20, 19, 15, 9, 30, 17, 0, 17],
        [16, 17, 7, 14, 19, 15, 24, 11, 15, 0]
    ]
    
    n_friends = 9  # Friends 1 to 9 (locations 1 to 9)
    a0 = 540  # 9:00 AM in minutes
    
    # Time windows and min durations for each friend (location 1 to 9)
    win_start = [0] * 10
    win_end = [0] * 10
    min_dur = [0] * 10
    
    # Friend 1: Helen (Golden Gate Park)
    win_start[1] = 570    # 9:30 AM
    win_end[1] = 735      # 12:15 PM
    min_dur[1] = 45
    
    # Friend 2: Steven (The Castro)
    win_start[2] = 1215   # 8:15 PM
    win_end[2] = 1320     # 10:00 PM
    min_dur[2] = 105
    
    # Friend 3: Deborah (Bayview)
    win_start[3] = 510    # 8:30 AM
    win_end[3] = 720      # 12:00 PM
    min_dur[3] = 30
    
    # Friend 4: Matthew (Marina District)
    win_start[4] = 555    # 9:15 AM
    win_end[4] = 855      # 2:15 PM
    min_dur[4] = 45
    
    # Friend 5: Joseph (Union Square)
    win_start[5] = 855    # 2:15 PM
    win_end[5] = 1125     # 6:45 PM
    min_dur[5] = 120
    
    # Friend 6: Ronald (Sunset District)
    win_start[6] = 960    # 4:00 PM
    win_end[6] = 1245     # 8:45 PM
    min_dur[6] = 60
    
    # Friend 7: Robert (Alamo Square)
    win_start[7] = 1110   # 6:30 PM
    win_end[7] = 1275     # 9:15 PM
    min_dur[7] = 120
    
    # Friend 8: Rebecca (Financial District)
    win_start[8] = 885    # 2:45 PM
    win_end[8] = 975      # 4:15 PM
    min_dur[8] = 30
    
    # Friend 9: Elizabeth (Mission District)
    win_start[9] = 1110   # 6:30 PM
    win_end[9] = 1260     # 9:00 PM
    min_dur[9] = 120
    
    s = Solver()
    
    # Attendance variables for friends 1-9
    attend = [Bool(f"attend_{i+1}") for i in range(n_friends)]
    
    # Time variables for friends 1-9
    start = [Int(f"start_{i+1}") for i in range(n_friends)]
    end = [Int(f"end_{i+1}") for i in range(n_friends)]
    a = [Int(f"a_{i+1}") for i in range(n_friends)]  # arrival time
    
    # z_ij: from i (0-9) to j (1-9), i != j
    z = {}
    for i in range(10):
        for j in range(1, 10):
            if i != j:
                z[(i, j)] = Bool(f"z_{i}_{j}")
    
    # Meeting constraints
    for i in range(n_friends):
        loc = i + 1
        s.add(Implies(attend[i],
            And(
                a[i] >= 0,  # arrival time non-negative
                start[i] >= a[i],  # start after arrival
                start[i] >= win_start[loc],
                end[i] == start[i] + min_dur[loc],
                end[i] <= win_end[loc]
            )))
    
    # Constraints for z_ij
    # 1. Each attended meeting j has exactly one incoming edge
    for j in range(1, 10):
        idx_j = j - 1
        incoming = []
        for i in range(0, 10):
            if i != j:
                incoming.append(z[(i, j)])
        s.add(If(attend[idx_j], Sum([If(var, 1, 0) for var in incoming]) == 1, 
                                Sum([If(var, 1, 0) for var in incoming]) == 0))
    
    # 2. Each location i has at most one outgoing edge
    for i in range(0, 10):
        outgoing = []
        for j in range(1, 10):
            if i != j:
                outgoing.append(z[(i, j)])
        s.add(Sum([If(var, 1, 0) for var in outgoing]) <= 1)
    
    # 3. If z_ij is True, set arrival time for j and enforce attendance
    for j in range(1, 10):
        idx_j = j - 1
        for i in range(0, 10):
            if i != j:
                if i == 0:
                    s.add(Implies(z[(i, j)],
                        And(attend[idx_j],
                            a[idx_j] == a0 + T[i][j])))
                else:
                    idx_i = i - 1
                    s.add(Implies(z[(i, j)],
                        And(attend[idx_i], attend[idx_j],
                            a[idx_j] == end[idx_i] + T[i][j])))
    
    # Objective: maximize number of meetings
    obj = Sum([If(attend[i], 1, 0) for i in range(n_friends)])
    s.maximize(obj)
    
    if s.check() == sat:
        m = s.model()
        num_meetings = m.evaluate(obj)
        print(f"SOLUTION: We can meet {num_meetings} friends.")
        
        # Reconstruct the schedule path
        path = []
        current = 0
        while True:
            next_found = False
            for j in range(1, 10):
                if current != j:
                    if m.evaluate(z[(current, j)]):
                        path.append(j)
                        current = j
                        next_found = True
                        break
            if not next_found:
                break
        
        # Convert minutes to HH:MM format
        def minutes_to_time(mins):
            mins_val = mins.as_long() if isinstance(mins, IntNumRef) else int(str(mins))
            hours = mins_val // 60
            minutes = mins_val % 60
            return f"{hours:02d}:{minutes:02d}"
        
        # Print schedule for attended meetings
        schedule = []
        for loc in path:
            idx = loc - 1
            a_time = m.evaluate(a[idx])
            s_time = m.evaluate(start[idx])
            e_time = m.evaluate(end[idx])
            schedule.append((
                loc,
                minutes_to_time(a_time),
                minutes_to_time(s_time),
                minutes_to_time(e_time)
            ))
        
        # Print schedule in order
        print("Schedule:")
        for loc, arr, start_t, end_t in schedule:
            print(f"Location {loc}: Arrive at {arr}, Meet from {start_t} to {end_t}")
        
        # Print skipped meetings
        skipped = []
        for i in range(1, 10):
            if not m.evaluate(attend[i-1]):
                skipped.append(i)
        if skipped:
            print("Skipped meetings at locations:", skipped)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()