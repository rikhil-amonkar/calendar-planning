from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Financial', 'Fisherman', 'Presidio', 'Bayview',
        'Haight', 'Russian', 'Castro', 'Marina',
        'Richmond', 'Union', 'Sunset'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 10, 22, 19, 19, 11, 20, 15, 21, 9, 30],      # Financial
        [11, 0, 17, 26, 22, 7, 27, 9, 18, 13, 27],       # Fisherman
        [23, 19, 0, 31, 15, 14, 21, 11, 7, 22, 15],      # Presidio
        [19, 25, 32, 0, 19, 23, 19, 27, 25, 18, 23],    # Bayview
        [21, 23, 15, 18, 0, 17, 6, 17, 10, 19, 15],     # Haight
        [11, 7, 14, 23, 17, 0, 21, 7, 14, 10, 23],      # Russian
        [21, 24, 20, 19, 6, 18, 0, 21, 16, 19, 17],     # Castro
        [17, 10, 10, 27, 16, 8, 22, 0, 11, 16, 19],     # Marina
        [22, 18, 7, 27, 10, 13, 16, 9, 0, 21, 11],      # Richmond
        [9, 15, 24, 15, 18, 13, 17, 18, 20, 0, 27],    # Union
        [30, 29, 16, 22, 15, 24, 17, 21, 12, 30, 0]    # Sunset
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Mark': {'location': 'Fisherman', 'start': -45, 'end': 60, 'min': 30},
        'Stephanie': {'location': 'Presidio', 'start': 195, 'end': 360, 'min': 75},
        'Betty': {'location': 'Bayview', 'start': -105, 'end': 690, 'min': 15},
        'Lisa': {'location': 'Haight', 'start': 390, 'end': 570, 'min': 45},
        'William': {'location': 'Russian', 'start': 465, 'end': 600, 'min': 60},
        'Brian': {'location': 'Castro', 'start': 15, 'end': 255, 'min': 30},
        'Joseph': {'location': 'Marina', 'start': 105, 'end': 360, 'min': 90},
        'Ashley': {'location': 'Richmond', 'start': 45, 'end': 135, 'min': 45},
        'Patricia': {'location': 'Union', 'start': 450, 'end': 600, 'min': 120},
        'Karen': {'location': 'Sunset', 'start': 450, 'end': 780, 'min': 105}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Financial at 9:00 AM (time = 0)
    current_loc = 'Financial'
    
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
        current_loc = 'Financial'
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