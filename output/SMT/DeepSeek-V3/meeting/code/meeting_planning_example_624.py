from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = ['Golden', 'Haight', 'Fisherman', 'Castro', 'Chinatown', 
                    'Alamo', 'North', 'Russian']
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 7, 24, 13, 23, 10, 24, 19],    # Golden
        [7, 0, 23, 6, 19, 5, 19, 17],      # Haight
        [25, 22, 0, 26, 12, 20, 6, 7],     # Fisherman
        [11, 6, 24, 0, 20, 8, 20, 18],     # Castro
        [23, 19, 8, 22, 0, 17, 3, 7],      # Chinatown
        [9, 5, 19, 8, 16, 0, 15, 13],      # Alamo
        [22, 18, 5, 22, 6, 16, 0, 4],       # North
        [21, 17, 7, 21, 9, 15, 5, 0]       # Russian
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Carol': {'location': 'Haight', 'start': 750, 'end': 810, 'min': 60},
        'Laura': {'location': 'Fisherman', 'start': 165, 'end': 750, 'min': 60},
        'Karen': {'location': 'Castro', 'start': -105, 'end': 300, 'min': 75},
        'Elizabeth': {'location': 'Chinatown', 'start': 195, 'end': 750, 'min': 75},
        'Deborah': {'location': 'Alamo', 'start': 180, 'end': 360, 'min': 105},
        'Jason': {'location': 'North', 'start': 345, 'end': 540, 'min': 90},
        'Steven': {'location': 'Russian', 'start': 345, 'end': 510, 'min': 120}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Golden at 9:00 AM (time = 0)
    current_loc = 'Golden'
    
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
    
    # Count number of friends met
    s.add(met_friends == Sum([If(met[f], 1, 0) for f in friends]))
    
    # Total meeting time
    s.add(total_meet_time == Sum([meet_time[f] for f in friends]))
    
    # Optimization objectives (prioritize meeting more friends)
    s.maximize(met_friends * 1000 + total_meet_time)
    
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
        current_loc = 'Golden'
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