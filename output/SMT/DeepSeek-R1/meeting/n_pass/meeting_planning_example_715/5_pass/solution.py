from z3 import *
import json

def main():
    # Travel times between locations (0-indexed: 0=Presidio, 1-8=friend locations)
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
    
    # Friends data
    friends = [
        {"name": "Amanda", "location": 1, "start_avail": 14*60+45, "end_avail": 19*60+30, "min_duration": 105},
        {"name": "Melissa", "location": 2, "start_avail": 9*60+30, "end_avail": 17*60+0, "min_duration": 30},
        {"name": "Jeffrey", "location": 3, "start_avail": 12*60+45, "end_avail": 18*60+45, "min_duration": 120},
        {"name": "Matthew", "location": 4, "start_avail": 10*60+15, "end_avail": 13*60+15, "min_duration": 30},
        {"name": "Nancy", "location": 5, "start_avail": 17*60+0, "end_avail": 21*60+30, "min_duration": 105},
        {"name": "Karen", "location": 6, "start_avail": 17*60+30, "end_avail": 20*60+30, "min_duration": 105},
        {"name": "Robert", "location": 7, "start_avail": 11*60+15, "end_avail": 17*60+30, "min_duration": 120},
        {"name": "Joseph", "location": 8, "start_avail": 8*60+30, "end_avail": 21*60+15, "min_duration": 105}
    ]
    
    n = len(friends)
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
        
        # First meeting constraints
        f0 = friend_idx[0]
        travel0 = Int('travel0')
        # Get location index for first friend
        loc0 = friends[0]['location']  # Default, but we need symbolic lookup
        
        # Create a travel time lookup function
        def travel_time(from_idx, to_idx):
            # from_idx and to_idx are Z3 Int variables representing friend indices
            from_loc = [friends[i]['location'] for i in range(n)]
            to_loc = [friends[i]['location'] for i in range(n)]
            # Return T[from_loc][to_loc] but we need symbolic lookup
            return [T[from_loc[i]][to_loc[j]] for i in range(n) for j in range(n)][from_idx * n + to_idx]
        
        # Instead we precompute a travel matrix for friends (8x8)
        friend_travel = [[T[friends[i]['location']][friends[j]['location']] for j in range(n)] for i in range(n)]
        
        # First meeting travel time from Presidio (location 0) to friend
        solver.add(travel0 == T[0][friends[0]['location']])  # Will fix symbolically
        
        # Better: use a function to get travel time from Presidio to friend i
        def first_travel(i):
            return T[0][friends[i]['location']]
        
        # Similarly for inter-friend travel
        def inter_travel(i, j):
            return T[friends[i]['location']][friends[j]['location']]
        
        # First meeting constraints (symbolic)
        solver.add(s[0] >= start_presidio + first_travel(friend_idx[0]))
        solver.add(s[0] >= friends[friend_idx[0]]['start_avail'])
        solver.add(e[0] == s[0] + friends[friend_idx[0]]['min_duration'])
        solver.add(e[0] <= friends[friend_idx[0]]['end_avail'])
        
        # Subsequent meetings
        for i in range(1, m):
            prev = friend_idx[i-1]
            curr = friend_idx[i]
            travel = inter_travel(prev, curr)
            solver.add(s[i] >= e[i-1] + travel)
            solver.add(s[i] >= friends[curr]['start_avail'])
            solver.add(e[i] == s[i] + friends[curr]['min_duration'])
            solver.add(e[i] <= friends[curr]['end_avail'])
        
        # Check for valid schedule
        if solver.check() == sat:
            model = solver.model()
            opt = Optimize()
            
            # Add existing constraints
            for c in solver.assertions():
                opt.add(c)
                
            # Minimize the last meeting end time
            last_end = e[m-1]
            opt.minimize(last_end)
            
            if opt.check() == sat:
                model = opt.model()
                schedule = []
                for i in range(m):
                    idx_val = model.evaluate(friend_idx[i]).as_long()
                    friend = friends[idx_val]
                    start_val = model.evaluate(s[i]).as_long()
                    end_val = model.evaluate(e[i]).as_long()
                    
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