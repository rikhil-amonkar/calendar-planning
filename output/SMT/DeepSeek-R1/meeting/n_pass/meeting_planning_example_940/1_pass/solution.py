from z3 import *
import json

def main():
    # Friend data: name, location, start_avail (minutes from 9:00 AM), end_avail, min_dur
    friends_data = [
        {"name": "Kevin", "loc": "Mission District", "start_avail": 705, "end_avail": 765, "min_dur": 60},
        {"name": "Mark", "loc": "Fisherman's Wharf", "start_avail": 495, "end_avail": 660, "min_dur": 90},
        {"name": "Jessica", "loc": "Russian Hill", "start_avail": 0, "end_avail": 360, "min_dur": 120},
        {"name": "Jason", "loc": "Marina District", "start_avail": 375, "end_avail": 765, "min_dur": 120},
        {"name": "John", "loc": "North Beach", "start_avail": 45, "end_avail": 540, "min_dur": 15},
        {"name": "Karen", "loc": "Chinatown", "start_avail": 465, "end_avail": 600, "min_dur": 75},
        {"name": "Sarah", "loc": "Pacific Heights", "start_avail": 510, "end_avail": 555, "min_dur": 45},
        {"name": "Amanda", "loc": "The Castro", "start_avail": 660, "end_avail": 675, "min_dur": 60},
        {"name": "Nancy", "loc": "Nob Hill", "start_avail": 45, "end_avail": 240, "min_dur": 45},
        {"name": "Rebecca", "loc": "Sunset District", "start_avail": 27, "end_avail": 360, "min_dur": 75}
    ]
    
    loc_index_map = {
        "Union Square": 0,
        "Mission District": 1,
        "Fisherman's Wharf": 2,
        "Russian Hill": 3,
        "Marina District": 4,
        "North Beach": 5,
        "Chinatown": 6,
        "Pacific Heights": 7,
        "The Castro": 8,
        "Nob Hill": 9,
        "Sunset District": 10
    }
    
    travel_str = """Union Square to Mission District: 14
Union Square to Fisherman's Wharf: 15
Union Square to Russian Hill: 13
Union Square to Marina District: 18
Union Square to North Beach: 10
Union Square to Chinatown: 7
Union Square to Pacific Heights: 15
Union Square to The Castro: 17
Union Square to Nob Hill: 9
Union Square to Sunset District: 27
Mission District to Union Square: 15
Mission District to Fisherman's Wharf: 22
Mission District to Russian Hill: 15
Mission District to Marina District: 19
Mission District to North Beach: 17
Mission District to Chinatown: 16
Mission District to Pacific Heights: 16
Mission District to The Castro: 7
Mission District to Nob Hill: 12
Mission District to Sunset District: 24
Fisherman's Wharf to Union Square: 13
Fisherman's Wharf to Mission District: 22
Fisherman's Wharf to Russian Hill: 7
Fisherman's Wharf to Marina District: 9
Fisherman's Wharf to North Beach: 6
Fisherman's Wharf to Chinatown: 12
Fisherman's Wharf to Pacific Heights: 12
Fisherman's Wharf to The Castro: 27
Fisherman's Wharf to Nob Hill: 11
Fisherman's Wharf to Sunset District: 27
Russian Hill to Union Square: 10
Russian Hill to Mission District: 16
Russian Hill to Fisherman's Wharf: 7
Russian Hill to Marina District: 7
Russian Hill to North Beach: 5
Russian Hill to Chinatown: 9
Russian Hill to Pacific Heights: 7
Russian Hill to The Castro: 21
Russian Hill to Nob Hill: 5
Russian Hill to Sunset District: 23
Marina District to Union Square: 16
Marina District to Mission District: 20
Marina District to Fisherman's Wharf: 10
Marina District to Russian Hill: 8
Marina District to North Beach: 11
Marina District to Chinatown: 15
Marina District to Pacific Heights: 7
Marina District to The Castro: 22
Marina District to Nob Hill: 12
Marina District to Sunset District: 19
North Beach to Union Square: 7
North Beach to Mission District: 18
North Beach to Fisherman's Wharf: 5
North Beach to Russian Hill: 4
North Beach to Marina District: 9
North Beach to Chinatown: 6
North Beach to Pacific Heights: 8
North Beach to The Castro: 23
North Beach to Nob Hill: 7
North Beach to Sunset District: 27
Chinatown to Union Square: 7
Chinatown to Mission District: 17
Chinatown to Fisherman's Wharf: 8
Chinatown to Russian Hill: 7
Chinatown to Marina District: 12
Chinatown to North Beach: 3
Chinatown to Pacific Heights: 10
Chinatown to The Castro: 22
Chinatown to Nob Hill: 9
Chinatown to Sunset District: 29
Pacific Heights to Union Square: 12
Pacific Heights to Mission District: 15
Pacific Heights to Fisherman's Wharf: 13
Pacific Heights to Russian Hill: 7
Pacific Heights to Marina District: 6
Pacific Heights to North Beach: 9
Pacific Heights to Chinatown: 11
Pacific Heights to The Castro: 16
Pacific Heights to Nob Hill: 8
Pacific Heights to Sunset District: 21
The Castro to Union Square: 19
The Castro to Mission District: 7
The Castro to Fisherman's Wharf: 24
The Castro to Russian Hill: 18
The Castro to Marina District: 21
The Castro to North Beach: 20
The Castro to Chinatown: 22
The Castro to Pacific Heights: 16
The Castro to Nob Hill: 16
The Castro to Sunset District: 17
Nob Hill to Union Square: 7
Nob Hill to Mission District: 13
Nob Hill to Fisherman's Wharf: 10
Nob Hill to Russian Hill: 5
Nob Hill to Marina District: 11
Nob Hill to North Beach: 8
Nob Hill to Chinatown: 6
Nob Hill to Pacific Heights: 8
Nob Hill to The Castro: 17
Nob Hill to Sunset District: 24
Sunset District to Union Square: 30
Sunset District to Mission District: 25
Sunset District to Fisherman's Wharf: 29
Sunset District to Russian Hill: 24
Sunset District to Marina District: 21
Sunset District to North Beach: 28
Sunset District to Chinatown: 30
Sunset District to Pacific Heights: 21
Sunset District to The Castro: 17
Sunset District to Nob Hill: 27"""
    
    # Build travel_time matrix (11x11)
    travel_time = [[0] * 11 for _ in range(11)]
    lines = travel_str.strip().split('\n')
    for line in lines:
        line = line.strip()
        if not line:
            continue
        if line.endswith('.'):
            line = line[:-1]
        parts = line.split(':')
        if len(parts) < 2:
            continue
        route_str = parts[0].strip()
        time_val = int(parts[1].strip())
        if ' to ' not in route_str:
            continue
        from_str, to_str = route_str.split(' to ', 1)
        from_str = from_str.strip()
        to_str = to_str.strip()
        if from_str in loc_index_map and to_str in loc_index_map:
            i = loc_index_map[from_str]
            j = loc_index_map[to_str]
            travel_time[i][j] = time_val
    
    # Assign location indices to friends
    for friend in friends_data:
        friend['loc_index'] = loc_index_map[friend['loc']]
    
    n_friends = len(friends_data)
    n_positions = n_friends
    
    # Z3 variables
    pos = [Int(f'pos_{k}') for k in range(n_positions)]
    start = [Int(f'start_{k}') for k in range(n_positions)]
    meet = [Bool(f'meet_{i}') for i in range(n_friends)]
    
    s = Optimize()
    
    # Position constraints
    for k in range(n_positions):
        s.add(Or(pos[k] == -1, And(pos[k] >= 0, pos[k] < n_friends)))
    
    # Contiguous sequence
    for k in range(n_positions - 1):
        s.add(Implies(pos[k] == -1, pos[k+1] == -1))
    
    # Each friend at most once
    for i in range(n_friends):
        s.add(Sum([If(pos[k] == i, 1, 0) for k in range(n_positions)]) <= 1)
        s.add(meet[i] == Or([pos[k] == i for k in range(n_positions)]))
    
    # Time constraints
    for k in range(n_positions):
        # Constraints for each position if not -1
        for i in range(n_friends):
            # Time window constraints
            s.add(Implies(pos[k] == i,
                          And(start[k] >= friends_data[i]['start_avail'],
                              start[k] + friends_data[i]['min_dur'] <= friends_data[i]['end_avail'])))
            
            # Travel time constraints
            if k == 0:
                s.add(Implies(pos[k] == i, 
                              start[k] >= travel_time[0][friends_data[i]['loc_index']]))
            else:
                for j in range(n_friends):
                    s.add(Implies(And(pos[k-1] == j, pos[k] == i),
                                  start[k] >= start[k-1] + friends_data[j]['min_dur'] + travel_time[friends_data[j]['loc_index']][friends_data[i]['loc_index']]))
    
    # Maximize the number of meetings
    total_meetings = Sum([If(meet[i], 1, 0) for i in range(n_friends)])
    s.maximize(total_meetings)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for k in range(n_positions):
            pos_val = m.evaluate(pos[k])
            if pos_val.as_long() == -1:
                break
            idx = pos_val.as_long()
            friend = friends_data[idx]
            start_min = m.evaluate(start[k]).as_long()
            dur = friend['min_dur']
            # Convert to time string (from 9:00 AM)
            total_min = start_min
            hour = 9 + total_min // 60
            minute = total_min % 60
            start_time_str = f"{hour:02d}:{minute:02d}"
            end_min = start_min + dur
            hour_end = 9 + end_min // 60
            minute_end = end_min % 60
            end_time_str = f"{hour_end:02d}:{minute_end:02d}"
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": start_time_str,
                "end_time": end_time_str
            })
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()