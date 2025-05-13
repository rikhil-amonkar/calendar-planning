from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Marina', 'Richmond', 'Union', 'Nob', 
        'Fisherman', 'Golden', 'Embarcadero', 
        'Financial', 'North', 'Presidio'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 11, 16, 12, 10, 18, 14, 17, 11, 10],    # Marina District
        [9, 0, 21, 17, 18, 9, 19, 22, 17, 7],        # Richmond District
        [18, 20, 0, 9, 15, 22, 11, 9, 10, 24],       # Union Square
        [11, 14, 7, 0, 10, 17, 9, 9, 8, 17],         # Nob Hill
        [9, 18, 13, 11, 0, 25, 8, 11, 6, 17],        # Fisherman's Wharf
        [16, 7, 22, 20, 24, 0, 25, 26, 23, 11],      # Golden Gate Park
        [12, 21, 10, 10, 6, 25, 0, 5, 5, 20],        # Embarcadero
        [15, 21, 9, 8, 10, 23, 4, 0, 7, 22],         # Financial District
        [9, 18, 7, 7, 5, 22, 6, 8, 0, 17],           # North Beach
        [11, 7, 22, 18, 19, 12, 20, 23, 18, 0]       # Presidio
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Stephanie': {'location': 'Richmond', 'start': 435, 'end': 690, 'min': 75},
        'William': {'location': 'Union', 'start': 105, 'end': 510, 'min': 45},
        'Elizabeth': {'location': 'Nob', 'start': 195, 'end': 360, 'min': 105},
        'Joseph': {'location': 'Fisherman', 'start': 225, 'end': 300, 'min': 75},
        'Anthony': {'location': 'Golden', 'start': 240, 'end': 570, 'min': 75},
        'Barbara': {'location': 'Embarcadero', 'start': 615, 'end': 690, 'min': 75},
        'Carol': {'location': 'Financial', 'start': 165, 'end': 375, 'min': 60},
        'Sandra': {'location': 'North', 'start': 60, 'end': 210, 'min': 15},
        'Kenneth': {'location': 'Presidio', 'start': 735, 'end': 795, 'min': 45}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Marina District at 9:00 AM (time = 0)
    current_loc = 'Marina'
    
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
        current_loc = 'Marina'
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