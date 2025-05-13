from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Russian', 'Marina', 'Financial', 'Alamo', 'Golden',
        'Castro', 'Bayview', 'Sunset', 'Haight', 'Nob'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 7, 11, 15, 21, 21, 23, 23, 17, 5],      # Russian Hill
        [8, 0, 17, 15, 18, 22, 27, 19, 16, 12],      # Marina District
        [11, 15, 0, 17, 23, 20, 19, 30, 19, 8],      # Financial District
        [13, 15, 17, 0, 9, 8, 16, 16, 5, 11],        # Alamo Square
        [19, 16, 26, 9, 0, 13, 23, 10, 7, 20],        # Golden Gate Park
        [18, 21, 21, 8, 11, 0, 19, 17, 6, 16],       # The Castro
        [23, 27, 19, 16, 22, 19, 0, 23, 19, 20],     # Bayview
        [24, 21, 30, 17, 11, 17, 22, 0, 15, 27],     # Sunset District
        [17, 17, 21, 5, 7, 6, 18, 15, 0, 15],         # Haight-Ashbury
        [5, 11, 9, 11, 17, 17, 19, 24, 13, 0]         # Nob Hill
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Mark': {'location': 'Marina', 'start': 585, 'end': 720, 'min': 90},
        'Karen': {'location': 'Financial', 'start': 30, 'end': 225, 'min': 90},
        'Barbara': {'location': 'Alamo', 'start': 60, 'end': 570, 'min': 90},
        'Nancy': {'location': 'Golden', 'start': 465, 'end': 600, 'min': 105},
        'David': {'location': 'Castro', 'start': 0, 'end': 540, 'min': 120},
        'Linda': {'location': 'Bayview', 'start': 555, 'end': 645, 'min': 45},
        'Kevin': {'location': 'Sunset', 'start': 60, 'end': 465, 'min': 120},
        'Matthew': {'location': 'Haight', 'start': 75, 'end': 330, 'min': 45},
        'Andrew': {'location': 'Nob', 'start': 165, 'end': 405, 'min': 105}
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