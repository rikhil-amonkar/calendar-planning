from z3 import *
import json

def main():
    # Travel times between locations (9x9 matrix)
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
    
    # Friends data with availability and duration constraints
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
    
    # Precompute data arrays
    n = len(friends_data)
    first_travel_times = [T[0][f['location']] for f in friends_data]
    start_avails = [f['start_avail'] for f in friends_data]
    end_avails = [f['end_avail'] for f in friends_data]
    min_durations = [f['min_duration'] for f in friends_data]
    
    # Precompute inter-friend travel times (flat array)
    inter_travel_times = []
    for i in range(n):
        for j in range(n):
            loc_i = friends_data[i]['location']
            loc_j = friends_data[j]['location']
            inter_travel_times.append(T[loc_i][loc_j])
    
    start_presidio = 9 * 60  # 9:00 AM in minutes
    
    # Try scheduling from 8 down to 1 meetings
    schedule = None
    for m in range(n, 0, -1):
        s = [Int(f's_{i}') for i in range(m)]      # Start times
        e = [Int(f'e_{i}') for i in range(m)]      # End times
        friend_idx = [Int(f'f_{i}') for i in range(m)]  # Friend indices
        
        solver = Solver()
        
        # Friend indices must be distinct and within range
        for i in range(m):
            solver.add(friend_idx[i] >= 0, friend_idx[i] < n)
        solver.add(Distinct(friend_idx))
        
        # Create Z3 arrays for data lookup
        first_travel_arr = Array('first_travel', IntSort(), IntSort())
        start_avail_arr = Array('start_avail', IntSort(), IntSort())
        end_avail_arr = Array('end_avail', IntSort(), IntSort())
        min_duration_arr = Array('min_duration', IntSort(), IntSort())
        inter_travel_arr = Array('inter_travel', IntSort(), IntSort())
        
        # Initialize arrays
        for i in range(n):
            solver.add(first_travel_arr[i] == first_travel_times[i])
            solver.add(start_avail_arr[i] == start_avails[i])
            solver.add(end_avail_arr[i] == end_avails[i])
            solver.add(min_duration_arr[i] == min_durations[i])
        
        for idx in range(n*n):
            solver.add(inter_travel_arr[idx] == inter_travel_times[idx])
        
        # First meeting constraints
        f0 = friend_idx[0]
        travel0 = first_travel_arr[f0]
        solver.add(s[0] >= start_presidio + travel0)
        solver.add(s[0] >= start_avail_arr[f0])
        solver.add(e[0] == s[0] + min_duration_arr[f0])
        solver.add(e[0] <= end_avail_arr[f0])
        
        # Subsequent meetings
        for i in range(1, m):
            f_prev = friend_idx[i-1]
            f_curr = friend_idx[i]
            
            # Calculate flat index for inter-friend travel
            travel_idx = f_prev * n + f_curr
            travel_time = inter_travel_arr[travel_idx]
            
            solver.add(s[i] >= e[i-1] + travel_time)
            solver.add(s[i] >= start_avail_arr[f_curr])
            solver.add(e[i] == s[i] + min_duration_arr[f_curr])
            solver.add(e[i] <= end_avail_arr[f_curr])
        
        # Check for valid schedule
        if solver.check() == sat:
            model = solver.model()
            opt = Optimize()
            
            # Add existing constraints
            for c in solver.assertions():
                opt.add(c)
                
            # Minimize total start time
            total_start = Int('total_start')
            opt.add(total_start == sum(s))
            opt.minimize(total_start)
            
            if opt.check() == sat:
                model = opt.model()
                schedule = []
                for i in range(m):
                    idx_val = model.eval(friend_idx[i]).as_long()
                    friend = friends_data[idx_val]
                    start_val = model.eval(s[i]).as_long()
                    end_val = model.eval(e[i]).as_long()
                    
                    # Convert times to HH:MM format
                    start_str = f"{start_val//60:02d}:{start_val%60:02d}"
                    end_str = f"{end_val//60:02d}:{end_val%60:02d}"
                    
                    schedule.append({
                        "action": "meet",
                        "person": friend['name'],
                        "start_time": start_str,
                        "end_time": end_str
                    })
                break
    
    # Output result
    result = {"itinerary": schedule} if schedule else {"itinerary": []}
    print("SOLUTION:")
    print(json.dumps(result))

if __name__ == "__main__":
    main()