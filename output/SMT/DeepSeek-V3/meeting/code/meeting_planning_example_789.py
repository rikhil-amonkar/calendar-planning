from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Union', 'Russian', 'Alamo', 'Haight', 'Marina',
        'Bayview', 'Chinatown', 'Presidio', 'Sunset'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 13, 15, 18, 18, 15, 7, 24, 27],      # Union
        [10, 0, 15, 17, 7, 23, 9, 14, 23],       # Russian
        [14, 13, 0, 5, 15, 16, 15, 17, 16],      # Alamo
        [19, 17, 5, 0, 17, 18, 19, 15, 15],      # Haight
        [16, 8, 15, 16, 0, 27, 15, 10, 19],     # Marina
        [18, 23, 16, 19, 27, 0, 19, 32, 23],    # Bayview
        [7, 7, 17, 19, 12, 20, 0, 19, 29],      # Chinatown
        [22, 14, 19, 15, 11, 31, 21, 0, 15],    # Presidio
        [30, 24, 17, 15, 21, 22, 30, 16, 0]     # Sunset
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Betty': {'location': 'Russian', 'start': -120, 'end': 465, 'min': 105},
        'Melissa': {'location': 'Alamo', 'start': 30, 'end': 495, 'min': 105},
        'Joshua': {'location': 'Haight', 'start': 195, 'end': 540, 'min': 90},
        'Jeffrey': {'location': 'Marina', 'start': 195, 'end': 480, 'min': 45},
        'James': {'location': 'Bayview', 'start': -90, 'end': 660, 'min': 90},
        'Anthony': {'location': 'Chinatown', 'start': 165, 'end': 270, 'min': 75},
        'Timothy': {'location': 'Presidio', 'start': 210, 'end': 345, 'min': 90},
        'Emily': {'location': 'Sunset', 'start': 630, 'end': 750, 'min': 120}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Union at 9:00 AM (time = 0)
    current_loc = 'Union'
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