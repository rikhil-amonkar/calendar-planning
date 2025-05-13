from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Presidio', 'Marina', 'Castro', 'Fisherman', 'Bayview',
        'Pacific', 'Mission', 'Alamo', 'Golden'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 11, 21, 19, 31, 11, 26, 19, 12],    # Presidio
        [10, 0, 22, 10, 27, 7, 20, 15, 18],     # Marina
        [20, 21, 0, 24, 19, 16, 7, 8, 11],      # Castro
        [17, 9, 27, 0, 26, 12, 22, 21, 25],     # Fisherman
        [32, 27, 19, 25, 0, 23, 13, 16, 22],    # Bayview
        [11, 6, 16, 13, 22, 0, 15, 10, 15],     # Pacific
        [25, 19, 7, 22, 14, 16, 0, 11, 17],      # Mission
        [17, 15, 8, 19, 16, 10, 10, 0, 9],       # Alamo
        [11, 16, 13, 24, 23, 16, 17, 9, 0]       # Golden
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Amanda': {'location': 'Marina', 'start': 345, 'end': 570, 'min': 105},
        'Melissa': {'location': 'Castro', 'start': 30, 'end': 480, 'min': 30},
        'Jeffrey': {'location': 'Fisherman', 'start': 225, 'end': 465, 'min': 120},
        'Matthew': {'location': 'Bayview', 'start': 75, 'end': 255, 'min': 30},
        'Nancy': {'location': 'Pacific', 'start': 480, 'end': 750, 'min': 105},
        'Karen': {'location': 'Mission', 'start': 510, 'end': 630, 'min': 105},
        'Robert': {'location': 'Alamo', 'start': 135, 'end': 510, 'min': 120},
        'Joseph': {'location': 'Golden', 'start': -30, 'end': 735, 'min': 105}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Presidio at 9:00 AM (time = 0)
    current_loc = 'Presidio'
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
        current_loc = 'Presidio'
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