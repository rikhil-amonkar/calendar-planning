import itertools
from z3 import *
import json

def main():
    meetings = [
        ("Joseph", 0, 60, 23, 555),   # name, location_index, duration, available_start, available_end (max start time)
        ("Nancy", 1, 90, 120, 330),
        ("Jason", 2, 15, 465, 750),
        ("Jeffrey", 3, 45, 90, 360)
    ]
    
    travel_time_from_Bayview = [23, 16, 21, 19]
    
    # travel_time_between: T[i][j] = time from location i to j
    T = [
        [0, 15, 5, 11],   # from location0 (Russian Hill) to others
        [13, 0, 15, 17],   # from location1 (Alamo Square) to others
        [4, 16, 0, 8],     # from location2 (North Beach) to others
        [10, 17, 7, 0]     # from location3 (Financial District) to others
    ]
    
    s0, s1, s2, s3 = Ints('s0 s1 s2 s3')
    b0, b1, b2, b3 = Bools('b0 b1 b2 b3')
    s = [s0, s1, s2, s3]
    b = [b0, b1, b2, b3]
    
    disjuncts = []
    all_meetings = [0, 1, 2, 3]
    
    for subset_size in range(0, 5):
        for subset in itertools.combinations(all_meetings, subset_size):
            for order in itertools.permutations(subset):
                constraints = []
                for i in all_meetings:
                    if i in subset:
                        constraints.append(b[i] == True)
                    else:
                        constraints.append(b[i] == False)
                
                if subset_size == 0:
                    disjuncts.append(And(constraints))
                    continue
                    
                first_meeting = order[0]
                _, loc0, dur0, avail_start0, avail_end0 = meetings[first_meeting]
                travel0 = travel_time_from_Bayview[first_meeting]
                constraints.append(s[first_meeting] >= travel0)
                constraints.append(s[first_meeting] >= avail_start0)
                constraints.append(s[first_meeting] <= avail_end0)
                current_time = s[first_meeting] + dur0
                
                for idx in range(1, len(order)):
                    prev_meeting = order[idx-1]
                    curr_meeting = order[idx]
                    _, loc_curr, dur_curr, avail_start_curr, avail_end_curr = meetings[curr_meeting]
                    travel_time = T[prev_meeting][curr_meeting]
                    constraints.append(s[curr_meeting] >= current_time + travel_time)
                    constraints.append(s[curr_meeting] >= avail_start_curr)
                    constraints.append(s[curr_meeting] <= avail_end_curr)
                    current_time = s[curr_meeting] + dur_curr
                    
                disjuncts.append(And(constraints))
                
    opt = Optimize()
    opt.add(Or(disjuncts))
    opt.maximize(Sum([If(b_i, 1, 0) for b_i in b]))
    result = []
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for i in range(4):
            if model.evaluate(b[i]):
                start_val = model.evaluate(s[i])
                if is_int(start_val):
                    start_val = start_val.as_long()
                name, _, dur, _, _ = meetings[i]
                end_val = start_val + dur
                scheduled_meetings.append((name, start_val, end_val))
        scheduled_meetings.sort(key=lambda x: x[1])
        result = scheduled_meetings
    else:
        result = []
    
    itinerary = []
    for (name, start, end) in result:
        total_minutes_start = start
        hour_start = 9 + total_minutes_start // 60
        minute_start = total_minutes_start % 60
        start_str = f"{hour_start:02d}:{minute_start:02d}"
        
        total_minutes_end = end
        hour_end = 9 + total_minutes_end // 60
        minute_end = total_minutes_end % 60
        end_str = f"{hour_end:02d}:{minute_end:02d}"
        
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": start_str,
            "end_time": end_str
        })
    
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()