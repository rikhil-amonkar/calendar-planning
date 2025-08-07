from z3 import *
import json

def main():
    meetings_info = [
        ("Rebecca", "Fisherman's Wharf", 0, 135, 30),   # 0: Rebecca
        ("Stephanie", "Golden Gate Park", 120, 300, 105), # 1: Stephanie
        ("Karen", "Chinatown", 285, 450, 15),    # 2: Karen
        ("Brian", "Union Square", 360, 495, 30),    # 3: Brian
        ("Steven", "North Beach", 330, 705, 120)   # 4: Steven
    ]
    
    # Map location names to indices
    # 0: Financial District, 1: Golden Gate Park, 2: Chinatown, 3: Union Square, 4: Fisherman's Wharf, 5: North Beach
    loc_name_to_index = {
        "Financial District": 0,
        "Golden Gate Park": 1,
        "Chinatown": 2,
        "Union Square": 3,
        "Fisherman's Wharf": 4,
        "North Beach": 5
    }
    
    meeting_loc_indices = [
        loc_name_to_index["Fisherman's Wharf"],   # Rebecca
        loc_name_to_index["Golden Gate Park"],    # Stephanie
        loc_name_to_index["Chinatown"],           # Karen
        loc_name_to_index["Union Square"],        # Brian
        loc_name_to_index["North Beach"]          # Steven
    ]
    
    # Travel matrix: 6x6, [from][to]
    # Indices: 0: FD, 1: GGP, 2: CT, 3: US, 4: FW, 5: NB
    travel_matrix = [
        [0, 23, 5, 9, 10, 7],     # from FD (0)
        [26, 0, 23, 22, 24, 24],   # from GGP (1)
        [5, 23, 0, 7, 8, 3],       # from CT (2)
        [9, 22, 7, 0, 15, 10],     # from US (3)
        [11, 25, 12, 13, 0, 6],    # from FW (4)
        [8, 22, 6, 7, 5, 0]        # from NB (5)
    ]
    
    n_slots = 5
    n_meetings = 5
    s = Solver()
    
    slot_meeting = [Int(f'slot_meeting_{i}') for i in range(n_slots)]
    start_time = [Int(f'start_time_{i}') for i in range(n_slots)]
    
    meet_flags = [Bool(f'meet_{i}') for i in range(n_meetings)]
    
    for i in range(n_slots):
        s.add(Or(And(slot_meeting[i] >= 0, slot_meeting[i] < n_meetings), slot_meeting[i] == n_meetings))
    
    for i in range(n_meetings):
        in_slot = [slot_meeting[j] == i for j in range(n_slots)]
        s.add(meet_flags[i] == Or(in_slot))
        s.add(Implies(meet_flags[i], Sum([If(cond, 1, 0) for cond in in_slot]) == 1))
        s.add(Implies(Not(meet_flags[i]), Sum([If(cond, 1, 0) for cond in in_slot]) == 0))
    
    for i in range(n_slots-1):
        s.add(Implies(slot_meeting[i] == n_meetings, slot_meeting[i+1] == n_meetings))
    
    base = 0
    for idx in range(n_slots):
        if idx == 0:
            loc0 = Int('loc0')
            s.add(loc0 == If(slot_meeting[0] == n_meetings, 0,
                             meeting_loc_indices[slot_meeting[0]]))
            s.add(If(slot_meeting[0] == n_meetings, True,
                     And(
                         start_time[0] >= base + travel_matrix[0][loc0],
                         start_time[0] >= meetings_info[slot_meeting[0]][2],
                         start_time[0] + meetings_info[slot_meeting[0]][4] <= meetings_info[slot_meeting[0]][3]
                     )))
        else:
            loc_prev = Int(f'loc_prev_{idx}')
            loc_curr = Int(f'loc_curr_{idx}')
            s.add(loc_prev == If(slot_meeting[idx-1] == n_meetings, 0,
                                 meeting_loc_indices[slot_meeting[idx-1]]))
            s.add(loc_curr == If(slot_meeting[idx] == n_meetings, 0,
                                 meeting_loc_indices[slot_meeting[idx]]))
            s.add(If(slot_meeting[idx] == n_meetings, True,
                     And(
                         slot_meeting[idx-1] != n_meetings,
                         start_time[idx] >= start_time[idx-1] + meetings_info[slot_meeting[idx-1]][4] + travel_matrix[loc_prev][loc_curr],
                         start_time[idx] >= meetings_info[slot_meeting[idx]][2],
                         start_time[idx] + meetings_info[slot_meeting[idx]][4] <= meetings_info[slot_meeting[idx]][3]
                     )))
    
    total_meetings = Int('total_meetings')
    s.add(total_meetings == Sum([If(flag, 1, 0) for flag in meet_flags]))
    
    opt = Optimize()
    opt.add(s.assertions())
    opt.maximize(total_meetings)
    
    schedule = []
    if opt.check() == sat:
        model = opt.model()
        total_met = model.eval(total_meetings)
        for i in range(n_slots):
            meeting_idx_val = model.eval(slot_meeting[i])
            if meeting_idx_val.as_long() == n_meetings:
                continue
            meeting_idx = meeting_idx_val.as_long()
            start_val = model.eval(start_time[i]).as_long()
            duration = meetings_info[meeting_idx][4]
            end_val = start_val + duration
            start_hour = 9 + start_val // 60
            start_minute = start_val % 60
            end_hour = 9 + end_val // 60
            end_minute = end_val % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            schedule.append({
                "action": "meet",
                "person": meetings_info[meeting_idx][0],
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