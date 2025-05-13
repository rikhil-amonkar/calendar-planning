from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Castro', 'Marina', 'Presidio', 'North', 'Embarcadero',
        'Haight', 'Golden', 'Richmond', 'Alamo', 'Financial', 'Sunset'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 21, 20, 20, 22, 6, 11, 16, 8, 21, 17],     # Castro
        [22, 0, 10, 11, 14, 16, 18, 11, 15, 17, 19],    # Marina
        [21, 11, 0, 18, 20, 15, 12, 7, 19, 23, 15],      # Presidio
        [23, 9, 17, 0, 6, 18, 22, 18, 16, 8, 27],       # North
        [25, 12, 20, 5, 0, 21, 25, 21, 19, 5, 30],       # Embarcadero
        [6, 17, 15, 19, 20, 0, 7, 10, 5, 21, 15],       # Haight
        [13, 16, 11, 23, 25, 7, 0, 7, 9, 26, 10],        # Golden
        [16, 9, 7, 17, 19, 10, 9, 0, 13, 22, 11],        # Richmond
        [8, 15, 17, 15, 16, 5, 9, 11, 0, 17, 16],        # Alamo
        [20, 15, 22, 7, 4, 19, 23, 21, 17, 0, 30],       # Financial
        [17, 21, 16, 28, 30, 15, 11, 12, 17, 30, 0]      # Sunset
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Elizabeth': {'location': 'Marina', 'start': 600, 'end': 645, 'min': 105},
        'Joshua': {'location': 'Presidio', 'start': -30, 'end': 255, 'min': 105},
        'Timothy': {'location': 'North', 'start': 645, 'end': 780, 'min': 90},
        'David': {'location': 'Embarcadero', 'start': 105, 'end': 210, 'min': 30},
        'Kimberly': {'location': 'Haight', 'start': 465, 'end': 750, 'min': 75},
        'Lisa': {'location': 'Golden', 'start': 510, 'end': 645, 'min': 45},
        'Ronald': {'location': 'Richmond', 'start': -60, 'end': 90, 'min': 90},
        'Stephanie': {'location': 'Alamo', 'start': 390, 'end': 450, 'min': 30},
        'Helen': {'location': 'Financial', 'start': 510, 'end': 570, 'min': 45},
        'Laura': {'location': 'Sunset', 'start': 525, 'end': 675, 'min': 90}
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