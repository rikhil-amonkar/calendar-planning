from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Russian', 'Pacific', 'North', 'Golden', 'Embarcadero',
        'Haight', 'Fisherman', 'Mission', 'Alamo', 'Bayview', 'Richmond'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 7, 5, 21, 8, 17, 7, 16, 15, 23, 14],      # Russian
        [7, 0, 9, 15, 10, 11, 13, 15, 10, 22, 12],     # Pacific
        [4, 8, 0, 22, 6, 18, 5, 18, 16, 25, 18],       # North
        [19, 16, 23, 0, 25, 7, 24, 17, 9, 23, 7],      # Golden
        [8, 11, 5, 25, 0, 21, 6, 20, 19, 21, 21],      # Embarcadero
        [17, 12, 19, 7, 20, 0, 23, 11, 5, 18, 10],     # Haight
        [7, 12, 6, 25, 8, 22, 0, 22, 21, 26, 18],      # Fisherman
        [15, 16, 17, 17, 19, 12, 22, 0, 11, 14, 20],   # Mission
        [13, 10, 15, 9, 16, 5, 19, 10, 0, 16, 11],     # Alamo
        [23, 23, 22, 22, 19, 19, 25, 13, 16, 0, 25],   # Bayview
        [13, 10, 17, 9, 19, 10, 18, 20, 13, 27, 0]     # Richmond
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Emily': {'location': 'Pacific', 'start': 15, 'end': 285, 'min': 120},
        'Helen': {'location': 'North', 'start': 285, 'end': 525, 'min': 30},
        'Kimberly': {'location': 'Golden', 'start': 525, 'end': 615, 'min': 75},
        'James': {'location': 'Embarcadero', 'start': 90, 'end': 150, 'min': 30},
        'Linda': {'location': 'Haight', 'start': -90, 'end': 615, 'min': 15},
        'Paul': {'location': 'Fisherman', 'start': 345, 'end': 525, 'min': 90},
        'Anthony': {'location': 'Mission', 'start': -60, 'end': 345, 'min': 105},
        'Nancy': {'location': 'Alamo', 'start': -30, 'end': 285, 'min': 120},
        'William': {'location': 'Bayview', 'start': 510, 'end': 630, 'min': 120},
        'Margaret': {'location': 'Richmond', 'start': 375, 'end': 495, 'min': 45}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Russian at 9:00 AM (time = 0)
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