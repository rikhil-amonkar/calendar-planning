from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Richmond', 'Chinatown', 'Sunset', 'Alamo', 'Financial',
        'North', 'Embarcadero', 'Presidio', 'Golden', 'Bayview'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 20, 11, 13, 22, 17, 19, 7, 9, 27],     # Richmond District
        [20, 0, 29, 17, 5, 3, 5, 19, 23, 20],      # Chinatown
        [12, 30, 0, 17, 30, 28, 30, 16, 11, 22],   # Sunset District
        [11, 15, 16, 0, 17, 15, 16, 17, 9, 16],    # Alamo Square
        [21, 5, 30, 17, 0, 7, 4, 22, 23, 19],      # Financial District
        [18, 6, 27, 16, 8, 0, 6, 17, 22, 25],      # North Beach
        [21, 7, 30, 19, 5, 5, 0, 20, 25, 21],      # Embarcadero
        [7, 21, 15, 19, 23, 18, 20, 0, 12, 31],    # Presidio
        [7, 23, 10, 9, 26, 23, 25, 11, 0, 23],     # Golden Gate Park
        [25, 19, 23, 16, 19, 22, 19, 32, 22, 0]    # Bayview
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Robert': {'location': 'Chinatown', 'start': -75, 'end': 510, 'min': 120},
        'David': {'location': 'Sunset', 'start': 210, 'end': 525, 'min': 45},
        'Matthew': {'location': 'Alamo', 'start': -15, 'end': 285, 'min': 90},
        'Jessica': {'location': 'Financial', 'start': 30, 'end': 585, 'min': 45},
        'Melissa': {'location': 'North', 'start': -105, 'end': 465, 'min': 45},
        'Mark': {'location': 'Embarcadero', 'start': 375, 'end': 480, 'min': 45},
        'Deborah': {'location': 'Presidio', 'start': 600, 'end': 645, 'min': 45},
        'Karen': {'location': 'Golden', 'start': 630, 'end': 780, 'min': 120},
        'Laura': {'location': 'Bayview', 'start': 735, 'end': 795, 'min': 15}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Richmond District at 9:00 AM (time = 0)
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