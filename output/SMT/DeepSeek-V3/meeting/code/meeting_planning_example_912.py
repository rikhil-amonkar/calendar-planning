from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Union Square', 'Presidio', 'Alamo Square', 'Marina District', 
        'Financial District', 'Nob Hill', 'Sunset District', 'Chinatown',
        'Russian Hill', 'North Beach', 'Haight-Ashbury'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 24, 15, 18, 9, 9, 27, 7, 13, 10, 18],    # Union Square
        [22, 0, 19, 11, 23, 18, 15, 21, 14, 18, 15], # Presidio
        [14, 17, 0, 15, 17, 11, 16, 15, 13, 15, 5],  # Alamo Square
        [16, 10, 15, 0, 17, 12, 19, 15, 8, 11, 16],  # Marina District
        [9, 22, 17, 15, 0, 8, 30, 5, 11, 7, 19],     # Financial District
        [7, 17, 11, 11, 9, 0, 24, 6, 5, 8, 13],      # Nob Hill
        [30, 16, 17, 21, 30, 27, 0, 30, 24, 28, 15], # Sunset District
        [7, 19, 17, 12, 5, 9, 29, 0, 7, 3, 19],      # Chinatown
        [10, 14, 15, 7, 11, 5, 23, 9, 0, 5, 17],      # Russian Hill
        [7, 17, 16, 9, 8, 7, 27, 6, 4, 0, 18],        # North Beach
        [19, 15, 5, 17, 21, 15, 15, 19, 17, 19, 0]    # Haight-Ashbury
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Kimberly': {'location': 'Presidio', 'start': 390, 'end': 420, 'min': 15},
        'Elizabeth': {'location': 'Alamo Square', 'start': 615, 'end': 675, 'min': 15},
        'Joshua': {'location': 'Marina District', 'start': 90, 'end': 195, 'min': 45},
        'Sandra': {'location': 'Financial District', 'start': 630, 'end': 675, 'min': 45},
        'Kenneth': {'location': 'Nob Hill', 'start': 225, 'end': 645, 'min': 30},
        'Betty': {'location': 'Sunset District', 'start': 300, 'end': 540, 'min': 60},
        'Deborah': {'location': 'Chinatown', 'start': 375, 'end': 510, 'min': 15},
        'Barbara': {'location': 'Russian Hill', 'start': 390, 'end': 555, 'min': 120},
        'Steven': {'location': 'North Beach', 'start': 405, 'end': 525, 'min': 90},
        'Daniel': {'location': 'Haight-Ashbury', 'start': 450, 'end': 465, 'min': 15}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Union Square at 9:00 AM (time = 0)
    current_loc = 'Union Square'
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
        travel = travel_times[n_indices[current_loc]][n_indices[friends[f]['location']]
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
        current_loc = 'Union Square'
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