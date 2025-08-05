from z3 import *
import json

def main():
    # Travel times matrix: 9x9 (0:Presidio, 1:Marina, 2:Castro, 3:Wharf, 4:Bayview, 5:Pacific, 6:Mission, 7:Alamo, 8:Golden Gate)
    T = [
        [0, 11, 21, 19, 31, 11, 26, 19, 12],
        [10, 0, 22, 10, 27, 7, 20, 15, 18],
        [20, 21, 0, 24, 19, 16, 7, 8, 11],
        [17, 9, 27, 0, 26, 12, 22, 21, 25],
        [32, 27, 19, 25, 0, 23, 13, 16, 22],
        [11, 6, 16, 13, 22, 0, 15, 10, 15],
        [25, 19, 7, 22, 14, 16, 0, 11, 17],
        [17, 15, 8, 19, 16, 10, 10, 0, 9],
        [11, 16, 13, 24, 23, 16, 17, 9, 0]
    ]
    
    friends_data = [
        {"name": "Amanda", "location": 1, "start_avail": 14*60+45, "end_avail": 19*60+30, "min_duration": 105},
        {"name": "Melissa", "location": 2, "start_avail": 9*60+30, "end_avail": 17*60+0, "min_duration": 30},
        {"name": "Jeffrey", "location": 3, "start_avail": 12*60+45, "end_avail": 18*60+45, "min_duration": 120},
        {"name": "Matthew", "location": 4, "start_avail": 10*60+15, "end_avail": 13*60+15, "min_duration": 30},
        {"name": "Nancy", "location": 5, "start_avail": 17*60+0, "end_avail": 21*60+30, "min_duration": 105},
        {"name": "Karen", "location": 6, "start_avail": 17*60+30, "end_avail": 20*60+30, "min_duration": 105},
        {"name": "Robert", "location": 7, "start_avail": 11*60+15, "end_avail": 17*60+30, "min_duration": 120},
        {"name": "Joseph", "location": 8, "start_avail": 8*60+30, "end_avail": 21*60+15, "min_duration": 105}
    ]
    
    # Precompute first travel times: from Presidio (0) to each friend's location
    first_travel_times = [T[0][f['location']] for f in friends_data]
    
    # Precompute inter-travel times between friends: from friend i to friend j
    inter_travel_times = [[T[friends_data[i]['location']][friends_data[j]['location']] for j in range(8)] for i in range(8)]
    
    # Start time at Presidio: 9:00 AM = 540 minutes
    start_presidio = 540
    
    # Try from 8 meetings down to 1
    schedule = None
    for m in range(8, 0, -1):
        s = [Int(f's_{i}') for i in range(m)]
        e = [Int(f'e_{i}') for i in range(m)]
        friend_index = [Int(f'f_{i}') for i in range(m)]
        
        solver = Solver()
        
        # Each friend_index must be between 0 and 7
        for i in range(m):
            solver.add(friend_index[i] >= 0, friend_index[i] <= 7)
            
        # Distinct friend indices
        solver.add(Distinct(friend_index))
        
        # First meeting constraints
        # Travel time from Presidio to first friend
        travel0 = Int('travel0')
        cond0 = None
        for idx in range(8):
            t_val = first_travel_times[idx]
            if cond0 is None:
                cond0 = If(friend_index[0] == idx, t_val, 0)
            else:
                cond0 = If(friend_index[0] == idx, t_val, cond0)
        solver.add(travel0 == cond0)
        
        # Start time of first meeting: at least start_presidio + travel0 and at least the friend's start_avail
        s0_avail = Int('s0_avail')
        cond_s0_avail = None
        for idx in range(8):
            avail_val = friends_data[idx]['start_avail']
            if cond_s0_avail is None:
                cond_s0_avail = If(friend_index[0] == idx, avail_val, 0)
            else:
                cond_s0_avail = If(friend_index[0] == idx, avail_val, cond_s0_avail)
        solver.add(s0_avail == cond_s0_avail)
        solver.add(s[0] >= start_presidio + travel0)
        solver.add(s[0] >= s0_avail)
        
        # End time of first meeting: s0 + min_duration
        min_dur0 = Int('min_dur0')
        cond_dur0 = None
        for idx in range(8):
            dur_val = friends_data[idx]['min_duration']
            if cond_dur0 is None:
                cond_dur0 = If(friend_index[0] == idx, dur_val, 0)
            else:
                cond_dur0 = If(friend_index[0] == idx, dur_val, cond_dur0)
        solver.add(min_dur0 == cond_dur0)
        solver.add(e[0] == s[0] + min_dur0)
        
        # End time must be <= friend's end_avail
        end_avail0 = Int('end_avail0')
        cond_end0 = None
        for idx in range(8):
            end_val = friends_data[idx]['end_avail']
            if cond_end0 is None:
                cond_end0 = If(friend_index[0] == idx, end_val, 0)
            else:
                cond_end0 = If(friend_index[0] == idx, end_val, cond_end0)
        solver.add(end_avail0 == cond_end0)
        solver.add(e[0] <= end_avail0)
        
        # Subsequent meetings
        for i in range(1, m):
            # Travel time from friend i-1 to friend i
            travel_i = Int(f'travel_{i}')
            cond_travel_i = None
            for idx_prev in range(8):
                for idx_curr in range(8):
                    t_val = inter_travel_times[idx_prev][idx_curr]
                    if cond_travel_i is None:
                        cond_travel_i = If(And(friend_index[i-1] == idx_prev, friend_index[i] == idx_curr), t_val, 0)
                    else:
                        cond_travel_i = If(And(friend_index[i-1] == idx_prev, friend_index[i] == idx_curr), t_val, cond_travel_i)
            solver.add(travel_i == cond_travel_i)
            
            # Start time of meeting i: at least end of previous meeting + travel time
            solver.add(s[i] >= e[i-1] + travel_i)
            
            # Also, at least the start_avail of friend i
            s_i_avail = Int(f's_{i}_avail')
            cond_s_i_avail = None
            for idx in range(8):
                avail_val = friends_data[idx]['start_avail']
                if cond_s_i_avail is None:
                    cond_s_i_avail = If(friend_index[i] == idx, avail_val, 0)
                else:
                    cond_s_i_avail = If(friend_index[i] == idx, avail_val, cond_s_i_avail)
            solver.add(s_i_avail == cond_s_i_avail)
            solver.add(s[i] >= s_i_avail)
            
            # End time: s[i] + min_duration
            min_dur_i = Int(f'min_dur_{i}')
            cond_dur_i = None
            for idx in range(8):
                dur_val = friends_data[idx]['min_duration']
                if cond_dur_i is None:
                    cond_dur_i = If(friend_index[i] == idx, dur_val, 0)
                else:
                    cond_dur_i = If(friend_index[i] == idx, dur_val, cond_dur_i)
            solver.add(min_dur_i == cond_dur_i)
            solver.add(e[i] == s[i] + min_dur_i)
            
            # End time <= end_avail of friend i
            end_avail_i = Int(f'end_avail_{i}')
            cond_end_i = None
            for idx in range(8):
                end_val = friends_data[idx]['end_avail']
                if cond_end_i is None:
                    cond_end_i = If(friend_index[i] == idx, end_val, 0)
                else:
                    cond_end_i = If(friend_index[i] == idx, end_val, cond_end_i)
            solver.add(end_avail_i == cond_end_i)
            solver.add(e[i] <= end_avail_i)
        
        # Check feasibility
        if solver.check() == sat:
            # Use Optimize to minimize the sum of start times
            opt = Optimize()
            # Add all constraints from solver to opt
            for c in solver.assertions():
                opt.add(c)
            # Minimize the sum of start times
            total_start = Int('total_start')
            opt.add(total_start == Sum(s))
            opt.minimize(total_start)
            if opt.check() == sat:
                model = opt.model()
                schedule = []
                for i in range(m):
                    idx_val = model[friend_index[i]].as_long()
                    friend = friends_data[idx_val]
                    start_min = model[s[i]].as_long()
                    end_min = model[e[i]].as_long()
                    start_hour = start_min // 60
                    start_minute = start_min % 60
                    end_hour = end_min // 60
                    end_minute = end_min % 60
                    start_str = f"{start_hour:02d}:{start_minute:02d}"
                    end_str = f"{end_hour:02d}:{end_minute:02d}"
                    schedule.append({
                        "action": "meet",
                        "person": friend['name'],
                        "start_time": start_str,
                        "end_time": end_str
                    })
                break
    
    if schedule is None:
        schedule = []
    
    result = {"itinerary": schedule}
    print("SOLUTION:")
    print(json.dumps(result))

if __name__ == "__main__":
    main()