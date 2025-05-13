from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Chinatown', 'Mission', 'Alamo', 'Pacific',
        'Union', 'Golden', 'Sunset', 'Presidio'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 18, 17, 10, 7, 23, 29, 19],    # Chinatown
        [16, 0, 11, 16, 15, 17, 24, 25],    # Mission
        [16, 10, 0, 10, 14, 9, 16, 18],     # Alamo
        [11, 15, 10, 0, 12, 15, 21, 11],    # Pacific
        [7, 14, 15, 15, 0, 22, 26, 24],     # Union
        [23, 17, 10, 16, 22, 0, 10, 11],    # Golden
        [30, 24, 17, 21, 30, 11, 0, 16],    # Sunset
        [21, 26, 18, 11, 22, 12, 15, 0]     # Presidio
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'David': {'location': 'Mission', 'start': -60, 'end': 645, 'min': 45},
        'Kenneth': {'location': 'Alamo', 'start': 300, 'end': 645, 'min': 120},
        'John': {'location': 'Pacific', 'start': 480, 'end': 600, 'min': 15},
        'Charles': {'location': 'Union', 'start': 765, 'end': 825, 'min': 60},
        'Deborah': {'location': 'Golden', 'start': -120, 'end': 555, 'min': 90},
        'Karen': {'location': 'Sunset', 'start': 525, 'end': 675, 'min': 15},
        'Carol': {'location': 'Presidio', 'start': -45, 'end': 75, 'min': 30}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Chinatown at 9:00 AM (time = 0)
    current_loc = 'Chinatown'
    
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
        current_loc = 'Chinatown'
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