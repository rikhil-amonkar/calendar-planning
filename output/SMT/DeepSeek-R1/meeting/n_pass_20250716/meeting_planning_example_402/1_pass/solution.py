from z3 import *

def main():
    # Travel time matrix: [Golden Gate Park, Haight-Ashbury, Sunset District, Marina District, Financial District, Union Square]
    T = [
        [0, 7, 10, 16, 26, 22],
        [7, 0, 15, 17, 21, 17],
        [11, 15, 0, 21, 30, 30],
        [18, 16, 19, 0, 17, 16],
        [23, 19, 31, 15, 0, 9],
        [22, 18, 26, 18, 9, 0]
    ]
    
    # Friend data: [Matthew, Robert, Joseph, Patricia, Sarah]
    # Each friend: [location_index, min_duration, available_start, available_end]
    friends_data = [
        (3, 15, 555, 720),    # Matthew: Marina, 9:15AM to 12:00PM
        (5, 15, 615, 1305),    # Robert: Union Square, 10:15AM to 9:45PM
        (4, 30, 855, 1125),    # Joseph: Financial, 2:15PM to 6:45PM
        (2, 45, 1020, 1185),   # Patricia: Sunset, 5:00PM to 7:45PM
        (1, 105, 1020, 1290)   # Sarah: Haight, 5:00PM to 9:30PM
    ]
    loc = [data[0] for data in friends_data]
    duration = [data[1] for data in friends_data]
    available_start = [data[2] for data in friends_data]
    available_end = [data[3] for data in friends_data]
    friend_names = ["Matthew", "Robert", "Joseph", "Patricia", "Sarah"]
    
    # Create solver and variables
    opt = Optimize()
    n_friends = 5
    meet = [Bool(f"meet_{i}") for i in range(n_friends)]
    start = [Real(f"start_{i}") for i in range(n_friends)]
    seq = [Int(f"seq_{k}") for k in range(n_friends)]
    
    # Constraints for sequence variables: each seq[k] is in [-1, 4]
    for k in range(n_friends):
        opt.add(Or(seq[k] == -1, And(seq[k] >= 0, seq[k] < n_friends)))
    
    # Non-negative entries in seq must be distinct
    for k1 in range(n_friends):
        for k2 in range(k1 + 1, n_friends):
            opt.add(Implies(And(seq[k1] != -1, seq[k2] != -1), seq[k1] != seq[k2]))
    
    # Sequence must be contiguous: if seq[k] is -1, then all subsequent must be -1
    for k in range(n_friends - 1):
        opt.add(Implies(seq[k] == -1, seq[k + 1] == -1))
    
    # Each friend is met iff they appear in the sequence
    for i in range(n_friends):
        opt.add(meet[i] == Or([seq[k] == i for k in range(n_friends)]))
    
    # First meeting constraint: start time must be after 9:00AM + travel from Golden Gate Park
    for i in range(n_friends):
        opt.add(Implies(seq[0] == i, start[i] >= 540 + T[0][loc[i]]))
    
    # Constraints for consecutive meetings
    for k in range(n_friends - 1):
        for i in range(n_friends):
            for j in range(n_friends):
                if i == j:
                    continue
                opt.add(Implies(And(seq[k] == i, seq[k + 1] == j),
                                start[j] >= start[i] + duration[i] + T[loc[i]][loc[j]]))
    
    # Meeting availability constraints
    for i in range(n_friends):
        opt.add(Implies(meet[i], 
                        And(start[i] >= available_start[i],
                            start[i] + duration[i] <= available_end[i])))
    
    # Objective: maximize number of friends met
    num_meetings = Int("num_meetings")
    opt.add(num_meetings == Sum([If(meet[i], 1, 0) for i in range(n_friends)]))
    opt.maximize(num_meetings)
    
    # Solve and output results
    if opt.check() == sat:
        m = opt.model()
        num_met = m.eval(num_meetings)
        print(f"SOLUTION: We can meet {num_met} friends.")
        
        # Get the meeting schedule
        schedule = []
        for k in range(n_friends):
            seq_val = m.eval(seq[k])
            if seq_val.as_long() == -1:
                break
            friend_idx = seq_val.as_long()
            start_time = m.eval(start[friend_idx])
            # Convert minutes to time string
            total_min = start_time.as_fraction().numerator // start_time.as_fraction().denominator
            hours = total_min // 60
            minutes = total_min % 60
            start_str = f"{hours:02d}:{minutes:02d}"
            end_time = total_min + duration[friend_idx]
            end_hours = end_time // 60
            end_minutes = end_time % 60
            end_str = f"{end_hours:02d}:{end_minutes:02d}"
            schedule.append((friend_names[friend_idx], start_str, end_str))
        
        # Print schedule in order
        print("Schedule:")
        for idx, (name, start_str, end_str) in enumerate(schedule):
            print(f"  {idx + 1}. Meet {name} from {start_str} to {end_str}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()