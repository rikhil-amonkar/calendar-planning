from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods mapping
    neighborhoods = ['Sunset', 'Presidio', 'Nob', 'Pacific', 'Mission', 
                    'Marina', 'North', 'Russian', 'Richmond', 'Embarcadero', 'Alamo']
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 16, 27, 21, 25, 21, 28, 24, 12, 30, 17],  # Sunset
        [15, 0, 18, 11, 26, 11, 18, 14, 7, 20, 19],    # Presidio
        [24, 17, 0, 8, 13, 11, 8, 5, 14, 9, 11],       # Nob Hill
        [21, 11, 8, 0, 15, 6, 9, 7, 12, 10, 10],        # Pacific Heights
        [24, 25, 12, 16, 0, 19, 17, 15, 20, 19, 11],    # Mission District
        [19, 10, 12, 7, 20, 0, 11, 8, 11, 14, 15],      # Marina District
        [27, 17, 7, 8, 18, 9, 0, 4, 18, 6, 16],         # North Beach
        [23, 14, 5, 7, 16, 7, 5, 0, 14, 8, 15],         # Russian Hill
        [11, 7, 17, 10, 20, 9, 17, 13, 0, 19, 13],      # Richmond District
        [30, 20, 10, 11, 20, 12, 5, 8, 21, 0, 16],     # Embarcadero
        [16, 17, 11, 10, 10, 15, 15, 13, 11, 16, 0]     # Alamo Square
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Charles': {'location': 'Presidio', 'start': 255, 'end': 360, 'min': 105},
        'Robert': {'location': 'Nob', 'start': 255, 'end': 450, 'min': 90},
        'Nancy': {'location': 'Pacific', 'start': 345, 'end': 780, 'min': 105},
        'Brian': {'location': 'Mission', 'start': 390, 'end': 780, 'min': 60},
        'Kimberly': {'location': 'Marina', 'start': 480, 'end': 525, 'min': 75},
        'David': {'location': 'North', 'start': 345, 'end': 450, 'min': 75},
        'William': {'location': 'Russian', 'start': 210, 'end': 495, 'min': 120},
        'Jeffrey': {'location': 'Richmond', 'start': 180, 'end': 495, 'min': 45},
        'Karen': {'location': 'Embarcadero', 'start': 315, 'end': 645, 'min': 60},
        'Joshua': {'location': 'Alamo', 'start': 585, 'end': 780, 'min': 60}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Sunset District at 9:00 AM (time = 0)
    current_loc = 'Sunset'
    
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
        current_loc = 'Sunset'
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