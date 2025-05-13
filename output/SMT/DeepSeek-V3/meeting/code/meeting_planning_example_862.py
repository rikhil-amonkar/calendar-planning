from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Mission', 'Alamo', 'Presidio', 'Russian', 'North',
        'Golden', 'Richmond', 'Embarcadero', 'Financial', 'Marina'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 11, 25, 15, 17, 17, 20, 19, 15, 19],     # Mission
        [10, 0, 17, 13, 15, 9, 11, 16, 17, 15],       # Alamo
        [26, 19, 0, 14, 18, 12, 7, 20, 23, 11],       # Presidio
        [16, 15, 14, 0, 5, 21, 14, 8, 11, 7],         # Russian
        [18, 16, 17, 4, 0, 22, 18, 6, 8, 9],          # North
        [17, 9, 11, 19, 23, 0, 7, 25, 26, 16],        # Golden
        [20, 13, 7, 13, 17, 9, 0, 19, 22, 9],         # Richmond
        [20, 19, 20, 8, 5, 25, 21, 0, 5, 12],         # Embarcadero
        [17, 17, 22, 11, 7, 23, 21, 4, 0, 15],        # Financial
        [20, 15, 10, 8, 11, 18, 11, 14, 17, 0]        # Marina
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Laura': {'location': 'Alamo', 'start': 330, 'end': 375, 'min': 75},
        'Brian': {'location': 'Presidio', 'start': 75, 'end': 420, 'min': 30},
        'Karen': {'location': 'Russian', 'start': 540, 'end': 615, 'min': 90},
        'Stephanie': {'location': 'North', 'start': 75, 'end': 360, 'min': 75},
        'Helen': {'location': 'Golden', 'start': 150, 'end': 765, 'min': 120},
        'Sandra': {'location': 'Richmond', 'start': -60, 'end': 375, 'min': 30},
        'Mary': {'location': 'Embarcadero', 'start': 465, 'end': 585, 'min': 120},
        'Deborah': {'location': 'Financial', 'start': 600, 'end': 645, 'min': 105},
        'Elizabeth': {'location': 'Marina', 'start': -30, 'end': 255, 'min': 105}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Mission at 9:00 AM (time = 0)
    current_loc = 'Mission'
    
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
        current_loc = 'Mission'
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