from z3 import *
import json

def main():
    friends = ['Michelle', 'Robert', 'George', 'William']
    
    available_start = {
        'Michelle': 8*60+15,   # 8:15 -> 495 minutes
        'Robert': 9*60,         # 9:00 -> 540 minutes
        'George': 10*60+30,     # 10:30 -> 630 minutes
        'William': 18*60+30     # 18:30 -> 1110 minutes
    }
    available_end = {
        'Michelle': 14*60,      # 14:00 -> 840 minutes
        'Robert': 13*60+45,     # 13:45 -> 825 minutes
        'George': 18*60+45,     # 18:45 -> 1125 minutes
        'William': 20*60+45     # 20:45 -> 1245 minutes
    }
    
    min_time = {
        'Michelle': 15,
        'Robert': 30,
        'George': 30,
        'William': 105
    }
    
    travel_matrix = [
        [0, 30, 29, 16, 24],   # Sunset District (0)
        [29, 0, 8, 19, 7],      # Chinatown (1)
        [27, 12, 0, 17, 7],     # Fisherman's Wharf (2)
        [15, 21, 19, 0, 14],    # Presidio (3)
        [23, 9, 7, 14, 0]       # Russian Hill (4)
    ]
    
    start_to_friend = [
        travel_matrix[0][1],  # Sunset to Michelle (Chinatown) -> 30
        travel_matrix[0][2],  # Sunset to Robert (Fisherman's Wharf) -> 29
        travel_matrix[0][3],  # Sunset to George (Presidio) -> 16
        travel_matrix[0][4]   # Sunset to William (Russian Hill) -> 24
    ]
    
    friend_to_friend = [
        [travel_matrix[1][1], travel_matrix[1][2], travel_matrix[1][3], travel_matrix[1][4]],   # from Michelle (Chinatown)
        [travel_matrix[2][1], travel_matrix[2][2], travel_matrix[2][3], travel_matrix[2][4]],   # from Robert (Fisherman's Wharf)
        [travel_matrix[3][1], travel_matrix[3][2], travel_matrix[3][3], travel_matrix[3][4]],   # from George (Presidio)
        [travel_matrix[4][1], travel_matrix[4][2], travel_matrix[4][3], travel_matrix[4][4]]    # from William (Russian Hill)
    ]
    
    available_start_list = [available_start[f] for f in friends]
    available_end_list = [available_end[f] for f in friends]
    min_time_list = [min_time[f] for f in friends]
    
    s = Optimize()
    
    slots = [Int(f'slot_{i}') for i in range(4)]
    for slot in slots:
        s.add(slot >= 0)
        s.add(slot <= 4)
        
    for i in range(3):
        s.add(Implies(slots[i] == 4, slots[i+1] == 4))
        
    met = [Bool(f'met_{f}') for f in friends]
    for idx in range(len(friends)):
        s.add(met[idx] == Or([slots[i] == idx for i in range(4)]))
        
    for i in range(4):
        for j in range(i+1, 4):
            s.add(Implies(And(slots[i] != 4, slots[j] != 4), slots[i] != slots[j]))
            
    starts = [Int(f'start_{i}') for i in range(4)]
    ends = [Int(f'end_{i}') for i in range(4)]
    
    prev_time = 540  # 9:00 AM in minutes
    
    def get_value_from_list(lst, idx):
        return If(idx == 0, lst[0],
               If(idx == 1, lst[1],
               If(idx == 2, lst[2],
               If(idx == 3, lst[3],
               0))))
    
    def get_start_to_friend_time(f_index):
        return If(f_index == 0, start_to_friend[0],
               If(f_index == 1, start_to_friend[1],
               If(f_index == 2, start_to_friend[2],
               If(f_index == 3, start_to_friend[3],
               0))))
    
    def get_friend_to_friend_time(f1, f2):
        if_true = Or(f1 == 4, f2 == 4)
        cases = []
        values = []
        for i in range(4):
            for j in range(4):
                cases.append(And(f1 == i, f2 == j))
                values.append(friend_to_friend[i][j])
        non_empty_expr = values[15]
        for idx in range(14, -1, -1):
            non_empty_expr = If(cases[idx], values[idx], non_empty_expr)
        return If(if_true, 0, non_empty_expr)
    
    for i in range(4):
        f_index = slots[i]
        cond = (f_index != 4)
        
        if i == 0:
            travel_time = get_start_to_friend_time(f_index)
        else:
            travel_time = get_friend_to_friend_time(slots[i-1], f_index)
        
        arrival_time = prev_time + travel_time
        
        start_low = get_value_from_list(available_start_list, f_index)
        start_high = get_value_from_list(available_end_list, f_index)
        duration = get_value_from_list(min_time_list, f_index)
        
        meeting_start = If(cond, If(arrival_time > start_low, arrival_time, start_low), 0)
        meeting_end = If(cond, meeting_start + duration, 0)
        
        s.add(If(cond, meeting_end <= start_high, True))
        s.add(If(cond, And(starts[i] == meeting_start, ends[i] == meeting_end), And(starts[i] == 0, ends[i] == 0)))
        
        prev_time = If(cond, meeting_end, prev_time)
    
    total_met = Sum([If(met_i, 1, 0) for met_i in met])
    s.maximize(total_met)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(4):
            slot_val = m[slots[i]]
            if isinstance(slot_val, IntNumRef):
                slot_val_int = slot_val.as_long()
            else:
                slot_val_int = int(str(slot_val))
            if slot_val_int != 4:
                friend_name = friends[slot_val_int]
                start_val = m[starts[i]]
                end_val = m[ends[i]]
                start_min = start_val.as_long()
                end_min = end_val.as_long()
                
                start_hour = start_min // 60
                start_minute = start_min % 60
                end_hour = end_min // 60
                end_minute = end_min % 60
                
                start_time_str = f"{start_hour:02d}:{start_minute:02d}"
                end_time_str = f"{end_hour:02d}:{end_minute:02d}"
                
                itinerary.append({
                    "action": "meet",
                    "person": friend_name,
                    "start_time": start_time_str,
                    "end_time": end_time_str
                })
        
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()