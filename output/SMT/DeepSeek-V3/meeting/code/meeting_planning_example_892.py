from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Marina', 'Bayview', 'Sunset', 'Richmond', 'Nob',
        'Chinatown', 'Haight', 'North', 'Russian', 'Embarcadero'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 27, 19, 11, 12, 15, 16, 11, 8, 14],       # Marina
        [27, 0, 23, 25, 20, 19, 19, 22, 23, 19],       # Bayview
        [21, 22, 0, 12, 27, 30, 15, 28, 24, 30],       # Sunset
        [9, 27, 11, 0, 17, 20, 10, 17, 13, 19],        # Richmond
        [11, 19, 24, 14, 0, 6, 13, 8, 5, 9],           # Nob
        [12, 20, 29, 20, 9, 0, 19, 3, 7, 5],           # Chinatown
        [17, 18, 15, 10, 15, 19, 0, 19, 17, 20],       # Haight
        [9, 25, 27, 18, 7, 6, 18, 0, 4, 6],            # North
        [7, 23, 23, 14, 5, 9, 17, 5, 0, 8],            # Russian
        [12, 21, 30, 21, 10, 7, 21, 5, 8, 0]           # Embarcadero
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Charles': {'location': 'Bayview', 'start': 150, 'end': 270, 'min': 45},
        'Robert': {'location': 'Sunset', 'start': 345, 'end': 600, 'min': 30},
        'Karen': {'location': 'Richmond', 'start': 615, 'end': 750, 'min': 60},
        'Rebecca': {'location': 'Nob', 'start': 375, 'end': 570, 'min': 90},
        'Margaret': {'location': 'Chinatown', 'start': 255, 'end': 525, 'min': 120},
        'Patricia': {'location': 'Haight', 'start': 270, 'end': 570, 'min': 45},
        'Mark': {'location': 'North', 'start': 300, 'end': 510, 'min': 105},
        'Melissa': {'location': 'Russian', 'start': 240, 'end': 525, 'min': 30},
        'Laura': {'location': 'Embarcadero', 'start': -15, 'end': 255, 'min': 105}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Marina at 9:00 AM (time = 0)
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