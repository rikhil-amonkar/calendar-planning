from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Haight', 'Mission', 'Union', 'Pacific', 'Bayview', 
        'Fisherman', 'Marina', 'Richmond', 'Sunset', 'Golden'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 11, 19, 12, 18, 23, 17, 10, 15, 7],    # Haight
        [12, 0, 15, 16, 14, 22, 19, 20, 24, 17],    # Mission
        [18, 14, 0, 15, 15, 15, 18, 20, 27, 22],    # Union
        [11, 15, 12, 0, 22, 13, 6, 12, 21, 15],     # Pacific
        [19, 13, 18, 23, 0, 25, 27, 25, 23, 22],    # Bayview
        [22, 22, 13, 12, 26, 0, 9, 18, 27, 25],     # Fisherman
        [16, 20, 16, 7, 27, 10, 0, 11, 19, 18],     # Marina
        [10, 20, 21, 10, 27, 18, 9, 0, 11, 9],      # Richmond
        [15, 25, 30, 21, 22, 29, 21, 12, 0, 10],    # Sunset
        [7, 17, 22, 16, 23, 24, 16, 7, 10, 0]       # Golden
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Elizabeth': {'location': 'Mission', 'start': 90, 'end': 600, 'min': 90},
        'David': {'location': 'Union', 'start': 375, 'end': 540, 'min': 45},
        'Sandra': {'location': 'Pacific', 'start': -120, 'end': 600, 'min': 120},
        'Thomas': {'location': 'Bayview', 'start': 630, 'end': 690, 'min': 30},
        'Robert': {'location': 'Fisherman', 'start': 60, 'end': 300, 'min': 15},
        'Kenneth': {'location': 'Marina', 'start': 105, 'end': 180, 'min': 45},
        'Melissa': {'location': 'Richmond', 'start': 435, 'end': 540, 'min': 15},
        'Kimberly': {'location': 'Sunset', 'start': 75, 'end': 435, 'min': 105},
        'Amanda': {'location': 'Golden', 'start': -75, 'end': 585, 'min': 15}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Haight at 9:00 AM (time = 0)
    current_loc = 'Haight'
    friend_order = []
    
    # Track which friends we meet
    met = {f: Bool(f'met_{f}') for f in friends}
    
    for f in friends:
        # Can choose to meet or not meet each friend
        s.add(Implies(met[f], arrival[f] >= friends[f]['start']))
        s.add(Implies(met[f], arrival[f] <= friends[f]['end']))
        s.add(Implies(met[f], departure[f] >= friends[f]['start']))
        s.add(Implies(met[f], departure[f] <= friends[f]['end']))
        s.add(Implies(met[f], meet_time[f] == departure[f] - arrival[f]))
        s.add(Implies(met[f], meet_time[f] >= friends[f]['min']))
        s.add(Implies(Not(met[f]), meet_time[f] == 0))
        
        # Travel time from current location if we meet this friend
        travel = travel_times[n_indices[current_loc]][n_indices[friends[f]['location']]]
        s.add(Implies(met[f], arrival[f] >= current_time + travel))
        
        # If we meet this friend, update current time and location
        current_time = If(met[f], departure[f], current_time)
        current_loc = If(met[f], friends[f]['location'], current_loc)
        friend_order.append((f, met[f]))
    
    # Count number of friends met
    s.add(met_friends == Sum([If(met[f], 1, 0) for f in friends]))
    
    # Total meeting time
    s.add(total_meet_time == Sum([meet_time[f] for f in friends]))
    
    # Optimization objectives (prioritize meeting more friends)
    s.maximize(met_friends * 1000 + total_meet_time)  # Weight friends more than time
    
    # Solve
    if s.check() == sat:
        m = s.model()
        schedule = []
        total_met = 0
        total_time = 0
        
        for f in friends:
            if m.eval(met[f]):
                start = m.eval(arrival[f]).as_long()
                end = m.eval(departure[f]).as_long()
                duration = m.eval(meet_time[f]).as_long()
                schedule.append((f, friends[f]['location'], start, end, duration))
                total_met += 1
                total_time += duration
        
        # Sort by start time
        schedule.sort(key=lambda x: x[2])
        
        print("OPTIMAL SCHEDULE:")
        current_loc = 'Haight'
        current_time = 0
        for f, loc, start, end, duration in schedule:
            travel = travel_times[n_indices[current_loc]][n_indices[loc]]
            print(f"Travel from {current_loc} to {loc} ({travel} mins)")
            print(f"Meet {f} in {loc} from {minutes_to_time(start)} to {minutes_to_time(end)} ({duration} mins)")
            current_loc = loc
            current_time = end
        
        print(f"\nTotal friends met: {total_met}")
        print(f"Total meeting time: {total_time} minutes")
    else:
        print("No valid schedule found")

def minutes_to_time(minutes):
    hours = 9 + minutes // 60
    mins = minutes % 60
    ampm = "AM" if hours < 12 else "PM"
    if hours > 12:
        hours -= 12
    return f"{hours}:{mins:02d}{ampm}"

optimize_schedule()