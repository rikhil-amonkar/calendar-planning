from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Presidio', 'Haight', 'Nob', 'Russian', 'North',
        'Chinatown', 'Union', 'Embarcadero', 'Financial', 'Marina'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 15, 18, 14, 18, 21, 22, 20, 23, 11],    # Presidio
        [15, 0, 15, 17, 19, 19, 19, 20, 21, 17],     # Haight
        [17, 13, 0, 5, 8, 6, 7, 9, 9, 11],           # Nob
        [14, 17, 5, 0, 5, 9, 10, 8, 11, 7],          # Russian
        [17, 18, 7, 4, 0, 6, 7, 6, 8, 9],            # North
        [19, 19, 9, 7, 3, 0, 7, 5, 5, 12],           # Chinatown
        [24, 18, 9, 13, 10, 7, 0, 11, 9, 18],        # Union
        [20, 21, 10, 8, 5, 7, 10, 0, 5, 12],         # Embarcadero
        [22, 19, 8, 11, 7, 5, 9, 4, 0, 15],          # Financial
        [10, 16, 12, 8, 11, 15, 16, 14, 17, 0]       # Marina
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Karen': {'location': 'Haight', 'start': 720, 'end': 765, 'min': 45},
        'Jessica': {'location': 'Nob', 'start': 285, 'end': 720, 'min': 90},
        'Brian': {'location': 'Russian', 'start': 390, 'end': 645, 'min': 60},
        'Kenneth': {'location': 'North', 'start': 45, 'end': 720, 'min': 30},
        'Jason': {'location': 'Chinatown', 'start': -45, 'end': 165, 'min': 75},
        'Stephanie': {'location': 'Union', 'start': 345, 'end': 465, 'min': 105},
        'Kimberly': {'location': 'Embarcadero', 'start': 45, 'end': 630, 'min': 75},
        'Steven': {'location': 'Financial', 'start': -105, 'end': 735, 'min': 60},
        'Mark': {'location': 'Marina', 'start': 75, 'end': 240, 'min': 75}
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