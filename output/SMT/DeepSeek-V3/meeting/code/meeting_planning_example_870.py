from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Pacific', 'Marina', 'Castro', 'Richmond', 'Alamo',
        'Financial', 'Presidio', 'Mission', 'Nob', 'Russian'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 6, 16, 12, 10, 13, 11, 15, 8, 7],       # Pacific Heights
        [7, 0, 22, 11, 15, 17, 10, 20, 12, 8],      # Marina District
        [16, 21, 0, 16, 8, 21, 20, 7, 16, 18],      # The Castro
        [10, 9, 16, 0, 13, 22, 7, 20, 17, 13],     # Richmond District
        [10, 15, 8, 11, 0, 17, 17, 10, 11, 13],    # Alamo Square
        [13, 15, 20, 21, 17, 0, 22, 17, 8, 11],    # Financial District
        [11, 11, 21, 7, 19, 23, 0, 26, 18, 14],    # Presidio
        [16, 19, 7, 20, 11, 15, 25, 0, 12, 15],     # Mission District
        [8, 11, 17, 14, 11, 9, 17, 13, 0, 5],       # Nob Hill
        [7, 7, 21, 14, 15, 11, 14, 16, 5, 0]        # Russian Hill
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Linda': {'location': 'Marina', 'start': 540, 'end': 720, 'min': 30},
        'Kenneth': {'location': 'Castro', 'start': 345, 'end': 435, 'min': 30},
        'Kimberly': {'location': 'Richmond', 'start': 315, 'end': 720, 'min': 30},
        'Paul': {'location': 'Alamo', 'start': 720, 'end': 750, 'min': 15},
        'Carol': {'location': 'Financial', 'start': 75, 'end': 180, 'min': 60},
        'Brian': {'location': 'Presidio', 'start': 60, 'end': 750, 'min': 75},
        'Laura': {'location': 'Mission', 'start': 375, 'end': 570, 'min': 30},
        'Sandra': {'location': 'Nob', 'start': 15, 'end': 570, 'min': 60},
        'Karen': {'location': 'Russian', 'start': 570, 'end': 720, 'min': 75}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Pacific Heights at 9:00 AM (time = 0)
    current_loc = 'Pacific'
    
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
        current_loc = 'Pacific'
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