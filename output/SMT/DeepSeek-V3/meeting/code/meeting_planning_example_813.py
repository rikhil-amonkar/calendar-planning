from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Marina', 'Embarcadero', 'Bayview', 'Union', 'Chinatown',
        'Sunset', 'Golden', 'Financial', 'Haight', 'Mission'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 14, 27, 16, 15, 19, 18, 17, 16, 20],      # Marina
        [12, 0, 21, 10, 7, 30, 25, 5, 21, 20],        # Embarcadero
        [27, 19, 0, 18, 19, 23, 22, 19, 19, 13],      # Bayview
        [18, 11, 15, 0, 7, 27, 22, 9, 18, 14],        # Union
        [12, 5, 20, 7, 0, 29, 23, 5, 19, 17],         # Chinatown
        [21, 30, 22, 30, 30, 0, 11, 30, 15, 25],      # Sunset
        [16, 25, 23, 22, 23, 10, 0, 26, 7, 17],       # Golden
        [15, 4, 19, 9, 5, 30, 23, 0, 19, 17],         # Financial
        [17, 20, 18, 19, 19, 15, 7, 21, 0, 11],       # Haight
        [19, 19, 14, 15, 16, 24, 17, 15, 12, 0]       # Mission
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Joshua': {'location': 'Embarcadero', 'start': 45, 'end': 540, 'min': 105},
        'Jeffrey': {'location': 'Bayview', 'start': 45, 'end': 555, 'min': 75},
        'Charles': {'location': 'Union', 'start': 105, 'end': 555, 'min': 120},
        'Joseph': {'location': 'Chinatown', 'start': -120, 'end': 390, 'min': 60},
        'Elizabeth': {'location': 'Sunset', 'start': 0, 'end': 45, 'min': 45},
        'Matthew': {'location': 'Golden', 'start': 120, 'end': 570, 'min': 45},
        'Carol': {'location': 'Financial', 'start': 105, 'end': 135, 'min': 15},
        'Paul': {'location': 'Haight', 'start': 615, 'end': 690, 'min': 15},
        'Rebecca': {'location': 'Mission', 'start': 480, 'end': 645, 'min': 45}
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