from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Russian', 'Sunset', 'Union', 'Nob', 'Marina',
        'Richmond', 'Financial', 'Embarcadero', 'Castro', 'Alamo', 'Presidio'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 23, 10, 5, 7, 14, 11, 8, 21, 15, 14],    # Russian Hill
        [24, 0, 30, 27, 21, 12, 30, 30, 17, 17, 16],  # Sunset District
        [13, 27, 0, 9, 18, 20, 9, 11, 17, 15, 24],    # Union Square
        [5, 24, 7, 0, 11, 14, 9, 9, 17, 11, 17],      # Nob Hill
        [8, 19, 16, 12, 0, 11, 17, 14, 22, 15, 10],   # Marina District
        [13, 11, 21, 17, 9, 0, 22, 19, 16, 13, 7],    # Richmond District
        [11, 30, 9, 8, 15, 21, 0, 4, 20, 17, 22],     # Financial District
        [8, 30, 10, 10, 12, 21, 5, 0, 25, 19, 20],    # Embarcadero
        [18, 17, 19, 16, 21, 16, 21, 22, 0, 8, 20],   # The Castro
        [13, 16, 14, 11, 15, 11, 17, 16, 8, 0, 17],   # Alamo Square
        [14, 15, 22, 18, 11, 7, 23, 20, 21, 19, 0]    # Presidio
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'David': {'location': 'Sunset', 'start': 15, 'end': 780, 'min': 15},
        'Kenneth': {'location': 'Union', 'start': 735, 'end': 765, 'min': 15},
        'Patricia': {'location': 'Nob', 'start': 360, 'end': 495, 'min': 120},
        'Mary': {'location': 'Marina', 'start': 345, 'end': 405, 'min': 45},
        'Charles': {'location': 'Richmond', 'start': 495, 'end': 720, 'min': 15},
        'Joshua': {'location': 'Financial', 'start': 330, 'end': 435, 'min': 90},
        'Ronald': {'location': 'Embarcadero', 'start': 555, 'end': 645, 'min': 30},
        'George': {'location': 'Castro', 'start': 315, 'end': 540, 'min': 105},
        'Kimberly': {'location': 'Alamo', 'start': 0, 'end': 330, 'min': 105},
        'William': {'location': 'Presidio', 'start': -120, 'end': 225, 'min': 60}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Russian Hill at 9:00 AM (time = 0)
    current_loc = 'Russian'
    
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
        current_loc = 'Russian'
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