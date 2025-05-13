from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Marina', 'Mission', 'Fisherman', 'Presidio', 
        'Union', 'Sunset', 'Financial', 'Haight', 'Russian'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 20, 10, 10, 16, 19, 17, 16, 8],      # Marina
        [19, 0, 22, 25, 15, 24, 15, 12, 15],      # Mission
        [9, 22, 0, 17, 13, 27, 11, 22, 7],       # Fisherman
        [11, 26, 19, 0, 22, 15, 23, 15, 14],     # Presidio
        [18, 14, 15, 24, 0, 27, 9, 18, 13],      # Union
        [21, 25, 29, 16, 30, 0, 30, 15, 24],     # Sunset
        [15, 17, 10, 22, 9, 30, 0, 19, 11],      # Financial
        [17, 11, 23, 15, 19, 15, 21, 0, 17],     # Haight
        [7, 16, 7, 14, 10, 23, 11, 17, 0]        # Russian
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Karen': {'location': 'Mission', 'start': 315, 'end': 780, 'min': 30},
        'Richard': {'location': 'Fisherman', 'start': 330, 'end': 450, 'min': 30},
        'Robert': {'location': 'Presidio', 'start': 1185, 'end': 1245, 'min': 60},
        'Joseph': {'location': 'Union', 'start': 165, 'end': 345, 'min': 120},
        'Helen': {'location': 'Sunset', 'start': 345, 'end': 645, 'min': 105},
        'Elizabeth': {'location': 'Financial', 'start': 60, 'end': 225, 'min': 75},
        'Kimberly': {'location': 'Haight', 'start': 315, 'end': 450, 'min': 105},
        'Ashley': {'location': 'Russian', 'start': 150, 'end': 750, 'min': 45}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Marina at 9:00 AM (time = 0)
    current_loc = 'Marina'
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
        current_loc = 'Marina'
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