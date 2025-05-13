from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Union', 'Castro', 'North', 'Embarcadero', 
        'Alamo', 'Nob', 'Presidio', 'Fisherman', 
        'Mission', 'Haight'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 17, 10, 11, 15, 9, 24, 15, 14, 18],    # Union Square
        [19, 0, 20, 22, 8, 16, 20, 24, 7, 6],       # The Castro
        [7, 23, 0, 6, 16, 7, 17, 5, 18, 18],        # North Beach
        [10, 25, 5, 0, 19, 10, 20, 6, 20, 21],      # Embarcadero
        [14, 8, 15, 16, 0, 11, 17, 19, 10, 5],      # Alamo Square
        [7, 17, 8, 9, 11, 0, 17, 10, 13, 13],       # Nob Hill
        [22, 21, 18, 20, 19, 18, 0, 19, 26, 15],    # Presidio
        [13, 27, 6, 8, 21, 11, 17, 0, 22, 22],      # Fisherman's Wharf
        [15, 7, 17, 19, 11, 12, 25, 22, 0, 12],     # Mission District
        [19, 6, 19, 20, 5, 15, 15, 23, 11, 0]       # Haight-Ashbury
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Melissa': {'location': 'Castro', 'start': 675, 'end': 735, 'min': 30},
        'Kimberly': {'location': 'North', 'start': -120, 'end': 90, 'min': 15},
        'Joseph': {'location': 'Embarcadero', 'start': 390, 'end': 570, 'min': 75},
        'Barbara': {'location': 'Alamo', 'start': 705, 'end': 765, 'min': 15},
        'Kenneth': {'location': 'Nob', 'start': 195, 'end': 375, 'min': 105},
        'Joshua': {'location': 'Presidio', 'start': 450, 'end': 495, 'min': 105},
        'Brian': {'location': 'Fisherman', 'start': 30, 'end': 390, 'min': 45},
        'Steven': {'location': 'Mission', 'start': 630, 'end': 720, 'min': 90},
        'Betty': {'location': 'Haight', 'start': 600, 'end': 690, 'min': 90}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Union Square at 9:00 AM (time = 0)
    current_loc = 'Union'
    
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
        current_loc = 'Union'
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