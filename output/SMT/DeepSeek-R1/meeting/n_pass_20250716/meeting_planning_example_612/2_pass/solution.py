from z3 import *

def build_single_choice(choice, values):
    expr = IntVal(0)
    n = len(values)
    for i in range(n-1, -1, -1):
        expr = If(choice == i, IntVal(values[i]), expr)
    return expr

def build_double_choice(choice1, choice2, values_matrix):
    expr = IntVal(0)
    n = len(values_matrix)
    for i in range(n-1, -1, -1):
        for j in range(n-1, -1, -1):
            expr = If(And(choice1 == i, choice2 == j), IntVal(values_matrix[i][j]), expr)
    return expr

def main():
    travel_matrix = [
        [0, 13, 18, 16, 16, 8, 17, 9],
        [15, 0, 14, 9, 23, 21, 8, 21],
        [18, 14, 0, 21, 15, 21, 20, 12],
        [17, 7, 19, 0, 29, 22, 5, 23],
        [17, 24, 16, 30, 0, 17, 31, 11],
        [8, 18, 20, 20, 17, 0, 22, 11],
        [19, 8, 20, 7, 30, 25, 0, 25],
        [10, 19, 11, 23, 10, 13, 25, 0]
    ]
    
    friends = [
        ("Emily", 195, 315, 105, 1),
        ("Mark", 345, 630, 60, 2),
        ("Deborah", 0, 390, 45, 3),
        ("Margaret", 750, 810, 60, 4),
        ("George", 0, 315, 60, 5),
        ("Andrew", 675, 780, 75, 6),
        ("Steven", 135, 735, 105, 7)
    ]
    n_friends = len(friends)
    max_positions = n_friends
    
    names = [f[0] for f in friends]
    window_start = [f[1] for f in friends]
    window_end = [f[2] for f in friends]
    min_duration = [f[3] for f in friends]
    loc_index = [f[4] for f in friends]
    
    travel_from_start = [travel_matrix[0][loc_index[i]] for i in range(n_friends)]
    travel_friend = []
    for i in range(n_friends):
        row = []
        for j in range(n_friends):
            row.append(travel_matrix[loc_index[i]][loc_index[j]])
        travel_friend.append(row)
    
    s = Solver()
    seq = [Int('seq_%d' % p) for p in range(max_positions)]
    meet = [Bool('meet_%d' % i) for i in range(n_friends)]
    start_time = [Int('start_time_%d' % p) for p in range(max_positions)]
    
    for p in range(max_positions):
        s.add(Or(seq[p] == -1, And(seq[p] >= 0, seq[p] < n_friends)))
        if p > 0:
            s.add(If(seq[p] != -1, seq[p-1] != -1, True))
            s.add(If(seq[p-1] == -1, seq[p] == -1, True))
    
    for i in range(n_friends):
        s.add(meet[i] == Or([seq[p] == i for p in range(max_positions)]))
    
    for p in range(max_positions):
        for q in range(p+1, max_positions):
            s.add(If(And(seq[p] >= 0, seq[q] >= 0), seq[p] != seq[q], True))
    
    for p in range(max_positions):
        if p == 0:
            friend0 = seq[0]
            travel0 = build_single_choice(friend0, travel_from_start)
            min_dur0 = build_single_choice(friend0, min_duration)
            win_start0 = build_single_choice(friend0, window_start)
            win_end0 = build_single_choice(friend0, window_end)
            
            s.add(If(friend0 >= 0,
                     And(
                         start_time[0] == If(travel0 >= win_start0, travel0, win_start0),
                         start_time[0] >= win_start0,
                         start_time[0] + min_dur0 <= win_end0
                     ),
                     True
                  ))
        else:
            friend_prev = seq[p-1]
            friend_curr = seq[p]
            travel_time = build_double_choice(friend_prev, friend_curr, travel_friend)
            min_dur_prev = build_single_choice(friend_prev, min_duration)
            min_dur_curr = build_single_choice(friend_curr, min_duration)
            win_start_curr = build_single_choice(friend_curr, window_start)
            win_end_curr = build_single_choice(friend_curr, window_end)
            
            arrival_p = start_time[p-1] + min_dur_prev + travel_time
            s.add(If(And(friend_curr >= 0, friend_prev >= 0),
                     And(
                         start_time[p] == If(arrival_p >= win_start_curr, arrival_p, win_start_curr),
                         start_time[p] >= win_start_curr,
                         start_time[p] + min_dur_curr <= win_end_curr
                     ),
                     True
                  ))
    
    num_meetings = Int('num_meetings')
    s.add(num_meetings == Sum([If(meet[i], 1, 0) for i in range(n_friends)]))
    
    objective = Maximize(num_meetings)
    opt = Optimize()
    opt.add(s.assertions())
    opt.maximize(num_meetings)
    
    if opt.check() == sat:
        m = opt.model()
        num_met = m.evaluate(num_meetings)
        print(f"Maximum number of meetings: {num_met}")
        schedule = []
        for p in range(max_positions):
            friend_idx_val = m.evaluate(seq[p])
            if friend_idx_val.as_long() == -1:
                break
            friend_idx = friend_idx_val.as_long()
            friend_name = names[friend_idx]
            st_val = m.evaluate(start_time[p])
            st = st_val.as_long()
            schedule.append((p, friend_name, st))
        print("Schedule (times from 9:00 AM in minutes):")
        for pos, name, start in schedule:
            total_minutes = start
            hours = total_minutes // 60
            minutes = total_minutes % 60
            print(f"Position {pos}: Meet {name} at {9+hours}:{minutes:02d}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()