from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Pacific', 'Golden', 'Castro', 'Bayview', 'Marina',
        'Union', 'Sunset', 'Alamo', 'Financial', 'Mission'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 15, 16, 22, 6, 12, 21, 10, 13, 15],    # Pacific
        [16, 0, 13, 23, 16, 22, 10, 9, 26, 17],     # Golden
        [16, 11, 0, 19, 21, 19, 17, 8, 21, 7],      # Castro
        [23, 22, 19, 0, 27, 18, 23, 16, 19, 13],     # Bayview
        [7, 18, 22, 27, 0, 16, 19, 15, 17, 20],     # Marina
        [15, 22, 17, 15, 18, 0, 27, 15, 9, 14],     # Union
        [21, 11, 17, 22, 21, 30, 0, 17, 30, 25],    # Sunset
        [10, 9, 8, 16, 15, 14, 16, 0, 17, 10],      # Alamo
        [13, 23, 20, 19, 15, 9, 30, 17, 0, 17],     # Financial
        [16, 17, 7, 14, 19, 15, 24, 11, 15, 0]      # Mission
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Helen': {'location': 'Golden', 'start': 30, 'end': 195, 'min': 45},
        'Steven': {'location': 'Castro', 'start': 675, 'end': 780, 'min': 105},
        'Deborah': {'location': 'Bayview', 'start': -30, 'end': 180, 'min': 30},
        'Matthew': {'location': 'Marina', 'start': 15, 'end': 255, 'min': 45},
        'Joseph': {'location': 'Union', 'start': 315, 'end': 525, 'min': 120},
        'Ronald': {'location': 'Sunset', 'start': 420, 'end': 585, 'min': 60},
        'Robert': {'location': 'Alamo', 'start': 570, 'end': 675, 'min': 120},
        'Rebecca': {'location': 'Financial', 'start': 345, 'end': 435, 'min': 30},
        'Elizabeth': {'location': 'Mission', 'start': 570, 'end': 720, 'min': 120}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Pacific at 9:00 AM (time = 0)
    current_loc = 'Pacific'
    
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
        current_loc = 'Pacific'
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