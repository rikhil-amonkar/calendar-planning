from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Presidio', 'Fisherman', 'Alamo', 'Financial', 'Union',
        'Sunset', 'Embarcadero', 'Golden', 'Chinatown', 'Richmond'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 19, 19, 23, 22, 15, 20, 12, 21, 7],      # Presidio
        [17, 0, 21, 11, 13, 27, 8, 25, 12, 18],       # Fisherman
        [17, 19, 0, 17, 14, 16, 16, 9, 15, 11],       # Alamo
        [22, 10, 17, 0, 9, 30, 4, 23, 5, 21],         # Financial
        [24, 15, 15, 9, 0, 27, 11, 22, 7, 20],        # Union
        [16, 29, 17, 30, 30, 0, 30, 11, 30, 12],      # Sunset
        [20, 6, 19, 5, 10, 30, 0, 25, 7, 21],         # Embarcadero
        [11, 24, 9, 26, 22, 10, 25, 0, 23, 7],        # Golden
        [19, 8, 17, 5, 7, 29, 5, 23, 0, 20],          # Chinatown
        [7, 18, 13, 22, 21, 11, 19, 9, 20, 0]         # Richmond
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Jeffrey': {'location': 'Fisherman', 'start': 75, 'end': 240, 'min': 90},
        'Ronald': {'location': 'Alamo', 'start': -75, 'end': 345, 'min': 120},
        'Jason': {'location': 'Financial', 'start': 105, 'end': 420, 'min': 105},
        'Melissa': {'location': 'Union', 'start': 525, 'end': 555, 'min': 15},
        'Elizabeth': {'location': 'Sunset', 'start': 345, 'end': 510, 'min': 105},
        'Margaret': {'location': 'Embarcadero', 'start': 255, 'end': 540, 'min': 90},
        'George': {'location': 'Golden', 'start': 600, 'end': 720, 'min': 75},
        'Richard': {'location': 'Chinatown', 'start': 30, 'end': 720, 'min': 15},
        'Laura': {'location': 'Richmond', 'start': 45, 'end': 540, 'min': 60}
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
    friend_order = []
    
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
        friend_order.append((f, met[f]))
    
    # Count number of friends met
    s.add(met_friends == Sum([If(met[f], 1, 0) for f in friends]))
    
    # Total meeting time
    s.add(total_meet_time == Sum([meet_time[f] for f in friends]))
    
    # Optimization objectives (prioritize meeting more friends)
    s.maximize(met_friends * 1000 + total_meet_time)  # Weight friends more than time
    
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