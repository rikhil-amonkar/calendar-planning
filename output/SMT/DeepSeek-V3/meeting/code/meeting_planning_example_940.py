from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Union', 'Mission', 'Fisherman', 'Russian', 'Marina',
        'North', 'Chinatown', 'Pacific', 'Castro', 'Nob', 'Sunset'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 14, 15, 13, 18, 10, 7, 15, 17, 9, 27],    # Union Square
        [15, 0, 22, 15, 19, 17, 16, 16, 7, 12, 24],    # Mission District
        [13, 22, 0, 7, 9, 6, 12, 12, 27, 11, 27],      # Fisherman's Wharf
        [10, 16, 7, 0, 7, 5, 9, 7, 21, 5, 23],         # Russian Hill
        [16, 20, 10, 8, 0, 11, 15, 7, 22, 12, 19],     # Marina District
        [7, 18, 5, 4, 9, 0, 6, 8, 23, 7, 27],          # North Beach
        [7, 17, 8, 7, 12, 3, 0, 10, 22, 9, 29],        # Chinatown
        [12, 15, 13, 7, 6, 9, 11, 0, 16, 8, 21],       # Pacific Heights
        [19, 7, 24, 18, 21, 20, 22, 16, 0, 16, 17],    # The Castro
        [7, 13, 10, 5, 11, 8, 6, 8, 17, 0, 24],        # Nob Hill
        [30, 25, 29, 24, 21, 28, 30, 21, 17, 27, 0]    # Sunset District
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Kevin': {'location': 'Mission', 'start': 705, 'end': 765, 'min': 60},
        'Mark': {'location': 'Fisherman', 'start': 495, 'end': 600, 'min': 90},
        'Jessica': {'location': 'Russian', 'start': 0, 'end': 360, 'min': 120},
        'Jason': {'location': 'Marina', 'start': 375, 'end': 645, 'min': 120},
        'John': {'location': 'North', 'start': 45, 'end': 540, 'min': 15},
        'Karen': {'location': 'Chinatown', 'start': 465, 'end': 600, 'min': 75},
        'Sarah': {'location': 'Pacific', 'start': 510, 'end': 555, 'min': 45},
        'Amanda': {'location': 'Castro', 'start': 660, 'end': 705, 'min': 60},
        'Nancy': {'location': 'Nob', 'start': 45, 'end': 240, 'min': 45},
        'Rebecca': {'location': 'Sunset', 'start': -15, 'end': 360, 'min': 75}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Union Square at 9:00 AM (time = 0)
    current_loc = 'Union'
    
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
        current_loc = 'Union'
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