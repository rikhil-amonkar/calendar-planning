from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Castro', 'North', 'Golden', 'Embarcadero', 'Haight',
        'Richmond', 'Nob', 'Marina', 'Presidio', 'Union', 'Financial'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 20, 11, 22, 6, 16, 16, 21, 20, 19, 21],      # Castro
        [23, 0, 22, 6, 18, 18, 7, 9, 17, 7, 8],          # North
        [13, 23, 0, 25, 7, 7, 20, 16, 11, 22, 26],       # Golden
        [25, 5, 25, 0, 21, 21, 10, 12, 20, 10, 5],       # Embarcadero
        [6, 19, 7, 20, 0, 10, 15, 17, 15, 19, 21],       # Haight
        [16, 17, 9, 19, 10, 0, 17, 9, 7, 21, 22],        # Richmond
        [17, 8, 17, 9, 13, 14, 0, 11, 17, 7, 9],         # Nob
        [22, 11, 18, 14, 16, 11, 12, 0, 10, 16, 17],     # Marina
        [21, 18, 12, 20, 15, 7, 18, 11, 0, 22, 23],      # Presidio
        [17, 10, 22, 11, 18, 20, 9, 18, 24, 0, 9],       # Union
        [20, 7, 23, 4, 19, 21, 8, 15, 22, 9, 0]           # Financial
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Steven': {'location': 'North', 'start': 510, 'end': 570, 'min': 15},
        'Sarah': {'location': 'Golden', 'start': 480, 'end': 555, 'min': 75},
        'Brian': {'location': 'Embarcadero', 'start': 315, 'end': 420, 'min': 105},
        'Stephanie': {'location': 'Haight', 'start': 75, 'end': 195, 'min': 75},
        'Melissa': {'location': 'Richmond', 'start': 300, 'end': 570, 'min': 30},
        'Nancy': {'location': 'Nob', 'start': -45, 'end': 225, 'min': 90},
        'David': {'location': 'Marina', 'start': 135, 'end': 255, 'min': 120},
        'James': {'location': 'Presidio', 'start': 360, 'end': 435, 'min': 120},
        'Elizabeth': {'location': 'Union', 'start': 150, 'end': 720, 'min': 60},
        'Robert': {'location': 'Financial', 'start': 255, 'end': 375, 'min': 45}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Castro at 9:00 AM (time = 0)
    current_loc = 'Castro'
    
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
        current_loc = 'Castro'
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