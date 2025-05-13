from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Embarcadero', 'Bayview', 'Chinatown', 'Alamo', 'Nob',
        'Presidio', 'Union', 'Castro', 'North', 'Fisherman', 'Marina'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 21, 7, 19, 10, 20, 10, 25, 5, 6, 12],    # Embarcadero
        [19, 0, 19, 16, 20, 32, 18, 19, 22, 25, 27],  # Bayview
        [5, 20, 0, 17, 9, 19, 7, 22, 3, 8, 12],       # Chinatown
        [16, 16, 15, 0, 11, 17, 14, 8, 15, 19, 15],   # Alamo Square
        [9, 19, 6, 11, 0, 17, 7, 17, 8, 10, 11],      # Nob Hill
        [20, 31, 21, 19, 18, 0, 22, 21, 18, 19, 11],  # Presidio
        [11, 15, 7, 15, 9, 24, 0, 17, 10, 15, 18],    # Union Square
        [22, 19, 22, 8, 16, 20, 19, 0, 20, 24, 21],   # The Castro
        [6, 25, 6, 16, 7, 17, 7, 23, 0, 5, 9],        # North Beach
        [8, 26, 12, 21, 11, 17, 13, 27, 6, 0, 9],     # Fisherman's Wharf
        [14, 27, 15, 15, 12, 10, 16, 22, 11, 10, 0]   # Marina District
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Matthew': {'location': 'Bayview', 'start': 615, 'end': 720, 'min': 120},
        'Karen': {'location': 'Chinatown', 'start': 615, 'end': 675, 'min': 90},
        'Sarah': {'location': 'Alamo', 'start': 660, 'end': 705, 'min': 105},
        'Jessica': {'location': 'Nob', 'start': 450, 'end': 525, 'min': 120},
        'Stephanie': {'location': 'Presidio', 'start': -30, 'end': 75, 'min': 60},
        'Mary': {'location': 'Union', 'start': 465, 'end': 690, 'min': 60},
        'Charles': {'location': 'Castro', 'start': 450, 'end': 720, 'min': 105},
        'Nancy': {'location': 'North', 'start': 345, 'end': 540, 'min': 15},
        'Thomas': {'location': 'Fisherman', 'start': 210, 'end': 480, 'min': 30},
        'Brian': {'location': 'Marina', 'start': 195, 'end': 420, 'min': 60}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Embarcadero at 9:00 AM (time = 0)
    current_loc = 'Embarcadero'
    
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
        current_loc = 'Embarcadero'
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