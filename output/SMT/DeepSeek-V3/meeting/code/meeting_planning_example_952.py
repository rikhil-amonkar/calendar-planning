from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Bayview', 'North', 'Fisherman', 'Haight', 'Nob',
        'Golden', 'Union', 'Alamo', 'Presidio', 'Chinatown', 'Pacific'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 22, 25, 19, 20, 22, 18, 16, 32, 19, 23],    # Bayview
        [25, 0, 5, 18, 7, 22, 7, 16, 17, 6, 8],         # North Beach
        [26, 6, 0, 22, 11, 25, 13, 21, 17, 12, 12],     # Fisherman's Wharf
        [18, 19, 23, 0, 15, 7, 19, 5, 15, 19, 12],      # Haight-Ashbury
        [19, 8, 10, 13, 0, 17, 7, 11, 17, 6, 8],        # Nob Hill
        [23, 23, 24, 7, 20, 0, 22, 9, 11, 23, 16],      # Golden Gate Park
        [15, 10, 15, 18, 9, 22, 0, 15, 24, 7, 15],      # Union Square
        [16, 15, 19, 5, 11, 9, 14, 0, 17, 15, 10],      # Alamo Square
        [31, 18, 19, 15, 18, 12, 22, 19, 0, 21, 11],    # Presidio
        [20, 3, 8, 19, 9, 23, 7, 17, 19, 0, 10],        # Chinatown
        [22, 9, 13, 11, 8, 15, 12, 10, 11, 11, 0]       # Pacific Heights
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Brian': {'location': 'North', 'start': 240, 'end': 540, 'min': 90},
        'Richard': {'location': 'Fisherman', 'start': 120, 'end': 165, 'min': 60},
        'Ashley': {'location': 'Haight', 'start': 360, 'end': 570, 'min': 90},
        'Elizabeth': {'location': 'Nob', 'start': 165, 'end': 450, 'min': 75},
        'Jessica': {'location': 'Golden', 'start': 660, 'end': 705, 'min': 105},
        'Deborah': {'location': 'Union', 'start': 510, 'end': 720, 'min': 60},
        'Kimberly': {'location': 'Alamo', 'start': 510, 'end': 615, 'min': 45},
        'Matthew': {'location': 'Presidio', 'start': -45, 'end': 0, 'min': 15},
        'Kenneth': {'location': 'Chinatown', 'start': 225, 'end': 510, 'min': 105},
        'Anthony': {'location': 'Pacific', 'start': 315, 'end': 420, 'min': 30}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Bayview at 9:00 AM (time = 0)
    current_loc = 'Bayview'
    
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
        current_loc = 'Bayview'
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