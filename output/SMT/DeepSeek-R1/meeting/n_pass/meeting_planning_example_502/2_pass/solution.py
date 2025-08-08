from z3 import *
import json

def main():
    n_meetings = 5
    n_slots = 5
    
    meeting_names = ["Rebecca", "Stephanie", "Karen", "Brian", "Steven"]
    meeting_locs = [4, 1, 2, 3, 5]  # 0:FD, 1:GGP, 2:CT, 3:US, 4:FW, 5:NB
    meeting_durations = [30, 105, 15, 30, 120]
    meeting_start_windows = [0, 120, 285, 360, 330]  # in minutes after 9:00AM
    meeting_end_windows = [135, 300, 450, 495, 705]  # in minutes after 9:00AM
    
    travel_matrix = [
        [0, 23, 5, 9, 10, 7],
        [26, 0, 23, 22, 24, 24],
        [5, 23, 0, 7, 8, 3],
        [9, 22, 7, 0, 15, 10],
        [11, 25, 12, 13, 0, 6],
        [8, 22, 6, 7, 5, 0]
    ]
    
    all_pairs = [(i, j) for i in range(6) for j in range(6)]
    
    def travel_time_expr(from_loc, to_loc):
        expr = travel_matrix[all_pairs[-1][0]][all_pairs[-1][1]]
        for idx in range(len(all_pairs)-2, -1, -1):
            i, j = all_pairs[idx]
            expr = If(And(from_loc == i, to_loc == j), travel_matrix[i][j], expr)
        return expr

    s = Solver()
    opt = Optimize()
    
    slot_meeting = [Int(f'slot_meeting_{i}') for i in range(n_slots)]
    start_time = [Int(f'start_time_{i}') for i in range(n_slots)]
    
    for i in range(n_slots):
        opt.add(Or(And(slot_meeting[i] >= 0, slot_meeting[i] < n_meetings), slot_meeting[i] == n_meetings))
    
    meet_flags = [Bool(f'meet_{i}') for i in range(n_meetings)]
    
    for i in range(n_meetings):
        in_slot = [slot_meeting[j] == i for j in range(n_slots)]
        opt.add(meet_flags[i] == Or(in_slot))
        opt.add(Implies(meet_flags[i], Sum([If(cond, 1, 0) for cond in in_slot]) == 1))
        opt.add(Implies(Not(meet_flags[i]), Sum([If(cond, 1, 0) for cond in in_slot]) == 0))
    
    for i in range(n_slots-1):
        opt.add(Implies(slot_meeting[i] == n_meetings, slot_meeting[i+1] == n_meetings))
    
    loc_vars = [Int(f'loc_{i}') for i in range(n_slots)]
    duration_vars = [Int(f'duration_{i}') for i in range(n_slots)]
    start_window_vars = [Int(f'start_window_{i}') for i in range(n_slots)]
    end_window_vars = [Int(f'end_window_{i}') for i in range(n_slots)]
    
    for i in range(n_slots):
        loc_expr = meeting_locs[0]
        dur_expr = meeting_durations[0]
        start_win_expr = meeting_start_windows[0]
        end_win_expr = meeting_end_windows[0]
        for m in range(1, n_meetings):
            loc_expr = If(slot_meeting[i] == m, meeting_locs[m], loc_expr)
            dur_expr = If(slot_meeting[i] == m, meeting_durations[m], dur_expr)
            start_win_expr = If(slot_meeting[i] == m, meeting_start_windows[m], start_win_expr)
            end_win_expr = If(slot_meeting[i] == m, meeting_end_windows[m], end_win_expr)
        loc_expr = If(slot_meeting[i] == n_meetings, 0, loc_expr)
        dur_expr = If(slot_meeting[i] == n_meetings, 0, dur_expr)
        start_win_expr = If(slot_meeting[i] == n_meetings, 0, start_win_expr)
        end_win_expr = If(slot_meeting[i] == n_meetings, 0, end_win_expr)
        opt.add(loc_vars[i] == loc_expr)
        opt.add(duration_vars[i] == dur_expr)
        opt.add(start_window_vars[i] == start_win_expr)
        opt.add(end_window_vars[i] == end_win_expr)
    
    for i in range(n_slots):
        if i == 0:
            opt.add(If(slot_meeting[i] == n_meetings, True,
                    And(
                        start_time[i] >= travel_time_expr(0, loc_vars[i]),
                        start_time[i] >= start_window_vars[i],
                        start_time[i] + duration_vars[i] <= end_window_vars[i]
                    )))
        else:
            opt.add(If(slot_meeting[i] == n_meetings, True,
                    And(
                        slot_meeting[i-1] != n_meetings,
                        start_time[i] >= start_time[i-1] + duration_vars[i-1] + travel_time_expr(loc_vars[i-1], loc_vars[i]),
                        start_time[i] >= start_window_vars[i],
                        start_time[i] + duration_vars[i] <= end_window_vars[i]
                    )))
    
    total_meetings = Int('total_meetings')
    opt.add(total_meetings == Sum([If(flag, 1, 0) for flag in meet_flags]))
    opt.maximize(total_meetings)
    
    schedule = []
    if opt.check() == sat:
        model = opt.model()
        for i in range(n_slots):
            meeting_idx_val = model.eval(slot_meeting[i])
            if meeting_idx_val.as_long() == n_meetings:
                continue
            meeting_idx = meeting_idx_val.as_long()
            start_val = model.eval(start_time[i]).as_long()
            duration_val = meeting_durations[meeting_idx]
            end_val = start_val + duration_val
            start_hour = 9 + start_val // 60
            start_minute = start_val % 60
            end_hour = 9 + end_val // 60
            end_minute = end_val % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            schedule.append({
                "action": "meet",
                "person": meeting_names[meeting_idx],
                "start_time": start_str,
                "end_time": end_str
            })
    else:
        schedule = []
    
    print('SOLUTION:')
    result = {"itinerary": schedule}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()