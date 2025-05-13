from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Richmond', 'Castro', 'Nob', 'Marina', 'Pacific', 
        'Haight', 'Mission', 'Chinatown', 'Russian', 'Alamo', 'Bayview'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 16, 17, 9, 10, 10, 20, 20, 13, 13, 27],     # Richmond
        [16, 0, 16, 21, 16, 6, 7, 22, 18, 8, 19],       # Castro
        [14, 17, 0, 11, 8, 13, 13, 6, 5, 11, 19],       # Nob
        [11, 22, 12, 0, 7, 16, 20, 15, 8, 15, 27],      # Marina
        [12, 16, 8, 6, 0, 11, 15, 11, 7, 10, 22],      # Pacific
        [10, 6, 15, 17, 12, 0, 11, 19, 17, 5, 18],     # Haight
        [20, 7, 12, 19, 16, 12, 0, 16, 15, 11, 14],     # Mission
        [20, 22, 9, 12, 10, 19, 17, 0, 7, 17, 20],      # Chinatown
        [14, 21, 5, 7, 7, 17, 16, 9, 0, 15, 23],       # Russian
        [11, 8, 11, 15, 10, 5, 10, 15, 13, 0, 16],     # Alamo
        [25, 19, 20, 27, 23, 19, 13, 19, 23, 16, 0]    # Bayview
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Matthew': {'location': 'Castro', 'start': 450, 'end': 600, 'min': 45},
        'Rebecca': {'location': 'Nob', 'start': 375, 'end': 495, 'min': 105},
        'Brian': {'location': 'Marina', 'start': 315, 'end': 720, 'min': 30},
        'Emily': {'location': 'Pacific', 'start': 135, 'end': 525, 'min': 15},
        'Karen': {'location': 'Haight', 'start': 165, 'end': 390, 'min': 30},
        'Stephanie': {'location': 'Mission', 'start': 240, 'end': 345, 'min': 75},
        'James': {'location': 'Chinatown', 'start': 330, 'end': 480, 'min': 120},
        'Steven': {'location': 'Russian', 'start': 300, 'end': 540, 'min': 30},
        'Elizabeth': {'location': 'Alamo', 'start': 240, 'end': 375, 'min': 120},
        'William': {'location': 'Bayview', 'start': 435, 'end': 495, 'min': 90}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Richmond at 9:00 AM (time = 0)
    current_loc = 'Richmond'
    
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
        current_loc = 'Richmond'
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