from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Nob', 'Embarcadero', 'Castro', 'Haight', 'Union',
        'North', 'Pacific', 'Chinatown', 'Golden', 'Marina', 'Russian'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 9, 17, 13, 7, 8, 8, 6, 17, 11, 5],        # Nob
        [10, 0, 25, 21, 10, 5, 11, 7, 25, 12, 8],     # Embarcadero
        [16, 22, 0, 6, 19, 20, 16, 22, 11, 21, 18],   # Castro
        [15, 20, 6, 0, 19, 19, 12, 19, 7, 17, 17],    # Haight
        [9, 11, 17, 18, 0, 10, 15, 7, 22, 18, 13],    # Union
        [7, 6, 23, 18, 7, 0, 8, 6, 22, 9, 4],         # North
        [8, 10, 16, 11, 12, 9, 0, 11, 15, 6, 7],      # Pacific
        [9, 5, 22, 19, 7, 3, 10, 0, 23, 12, 7],      # Chinatown
        [20, 25, 13, 7, 22, 23, 16, 23, 0, 16, 19],  # Golden
        [12, 14, 22, 16, 16, 11, 7, 15, 18, 0, 8],   # Marina
        [5, 8, 21, 17, 10, 5, 7, 9, 21, 7, 0]        # Russian
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Mary': {'location': 'Embarcadero', 'start': 660, 'end': 675, 'min': 75},
        'Kenneth': {'location': 'Castro', 'start': 135, 'end': 495, 'min': 30},
        'Joseph': {'location': 'Haight', 'start': 660, 'end': 720, 'min': 120},
        'Sarah': {'location': 'Union', 'start': 165, 'end': 330, 'min': 90},
        'Thomas': {'location': 'North', 'start': 615, 'end': 645, 'min': 15},
        'Daniel': {'location': 'Pacific', 'start': 285, 'end': 570, 'min': 15},
        'Richard': {'location': 'Chinatown', 'start': -60, 'end': 585, 'min': 30},
        'Mark': {'location': 'Golden', 'start': 510, 'end': 690, 'min': 120},
        'David': {'location': 'Marina', 'start': 660, 'end': 720, 'min': 60},
        'Karen': {'location': 'Russian', 'start': 255, 'end': 510, 'min': 120}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Nob at 9:00 AM (time = 0)
    current_loc = 'Nob'
    
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
        current_loc = 'Nob'
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