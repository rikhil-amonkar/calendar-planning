from z3 import *

def main():
    # Travel time matrix: 11x11 (0: Financial District, 1: Fisherman's Wharf, ..., 10: Sunset District)
    travel_time = [
        [0, 10, 22, 19, 19, 11, 20, 15, 21, 9, 30],
        [11, 0, 17, 26, 22, 7, 27, 9, 18, 13, 27],
        [23, 19, 0, 31, 15, 14, 21, 11, 7, 22, 15],
        [19, 25, 32, 0, 19, 23, 19, 27, 25, 18, 23],
        [21, 23, 15, 18, 0, 17, 6, 17, 10, 19, 15],
        [11, 7, 14, 23, 17, 0, 21, 7, 14, 10, 23],
        [21, 24, 20, 19, 6, 18, 0, 21, 16, 19, 17],
        [17, 10, 10, 27, 16, 8, 22, 0, 11, 16, 19],
        [22, 18, 7, 27, 10, 13, 16, 9, 0, 21, 11],
        [9, 15, 24, 15, 18, 13, 17, 18, 20, 0, 27],
        [30, 29, 16, 22, 15, 24, 17, 21, 12, 30, 0]
    ]
    
    # Friend information: name, location index, window start (minutes from 9:00 AM), window end, min duration
    names = ["Mark", "Stephanie", "Betty", "Lisa", "William", "Brian", "Joseph", "Ashley", "Patricia", "Karen"]
    location_index = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    window_start = [-45, 195, -105, 390, 585, 15, 105, 45, 450, 450]  # in minutes
    window_end = [60, 360, 690, 570, 660, 255, 360, 135, 660, 780]    # in minutes
    min_dur = [30, 75, 15, 45, 60, 30, 90, 45, 120, 105]              # in minutes

    n = len(names)
    meet = [Bool(f'meet_{i}') for i in range(n)]
    start = [Real(f'start_{i}') for i in range(n)]
    pos = [Int(f'pos_{i}') for i in range(n)]
    
    s = Solver()
    opt = Optimize()
    
    stephanie_index = names.index("Stephanie")
    
    for i in range(n):
        # If meeting friend i, enforce time window and travel from start
        travel_from_start = travel_time[0][location_index[i]]
        opt.add(Implies(meet[i], start[i] >= window_start[i]))
        if i == stephanie_index:
            opt.add(Implies(meet[i], start[i] + min_dur[i] < window_end[i]))
        else:
            opt.add(Implies(meet[i], start[i] + min_dur[i] <= window_end[i]))
        opt.add(Implies(meet[i], start[i] >= travel_from_start))
        opt.add(Implies(meet[i], And(pos[i] >= 1, pos[i] <= 10)))
    
    for i in range(n):
        for j in range(i+1, n):
            both_met = And(meet[i], meet[j])
            t_ij = travel_time[location_index[i]][location_index[j]]
            t_ji = travel_time[location_index[j]][location_index[i]]
            opt.add(Implies(both_met, 
                          Or(
                              And(pos[i] < pos[j], start[j] >= start[i] + min_dur[i] + t_ij),
                              And(pos[j] < pos[i], start[i] >= start[j] + min_dur[j] + t_ji)
                          )))
            opt.add(Implies(both_met, pos[i] != pos[j]))
    
    obj = Sum([If(meet[i], 1, 0) for i in range(n)])
    opt.maximize(obj)
    
    if opt.check() == sat:
        model = opt.model()
        total_meetings = 0
        result_schedule = []
        for i in range(n):
            if model.eval(meet[i]):
                total_meetings += 1
                s_val = model.eval(start[i])
                p_val = model.eval(pos[i])
                start_min = float(s_val.as_fraction()) if is_rational_value(s_val) else float(s_val.as_decimal(3))
                end_min = start_min + min_dur[i]
                result_schedule.append((p_val, names[i], start_min, end_min))
        
        result_schedule.sort(key=lambda x: int(str(x[0])))
        print("SOLUTION:")
        for pos_val, name, s_min, e_min in result_schedule:
            print(f"Meet {name} starting at {s_min:.2f} minutes after 9:00 AM, ending at {e_min:.2f} minutes after 9:00 AM")
        print(f"Total meetings: {total_meetings}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()