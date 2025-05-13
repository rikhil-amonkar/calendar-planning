from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Presidio', 'Pacific', 'Golden', 'Fisherman', 'Marina',
        'Alamo', 'Sunset', 'Nob', 'North'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 11, 12, 19, 11, 19, 15, 18, 18],      # Presidio
        [11, 0, 15, 13, 6, 10, 21, 8, 9],          # Pacific
        [11, 16, 0, 24, 16, 9, 10, 20, 23],         # Golden
        [17, 12, 25, 0, 9, 21, 27, 11, 6],          # Fisherman
        [10, 7, 18, 10, 0, 15, 19, 12, 11],         # Marina
        [17, 10, 9, 19, 15, 0, 16, 11, 15],         # Alamo
        [16, 21, 11, 29, 21, 17, 0, 27, 28],        # Sunset
        [17, 8, 17, 10, 11, 11, 24, 0, 8],          # Nob
        [17, 8, 22, 5, 9, 16, 27, 7, 0]             # North
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Kevin': {'location': 'Pacific', 'start': -105, 'end': -15, 'min': 90},
        'Michelle': {'location': 'Golden', 'start': 660, 'end': 720, 'min': 15},
        'Emily': {'location': 'Fisherman', 'start': 435, 'end': 540, 'min': 30},
        'Mark': {'location': 'Marina', 'start': 555, 'end': 645, 'min': 75},
        'Barbara': {'location': 'Alamo', 'start': 480, 'end': 600, 'min': 120},
        'Laura': {'location': 'Sunset', 'start': 600, 'end': 675, 'min': 75},
        'Mary': {'location': 'Nob', 'start': 510, 'end': 600, 'min': 45},
        'Helen': {'location': 'North', 'start': 120, 'end': 195, 'min': 45}
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