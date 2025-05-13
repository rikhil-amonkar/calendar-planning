from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = ['Castro', 'Bayview', 'Pacific', 'Alamo', 'Fisherman', 'Golden']
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 19, 16, 8, 24, 11],    # The Castro
        [20, 0, 23, 16, 25, 22],    # Bayview
        [16, 22, 0, 10, 13, 15],    # Pacific Heights
        [8, 16, 10, 0, 19, 9],      # Alamo Square
        [26, 26, 12, 20, 0, 25],    # Fisherman's Wharf
        [13, 23, 16, 10, 24, 0]     # Golden Gate Park
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Rebecca': {'location': 'Bayview', 'start': 0, 'end': 225, 'min': 90},
        'Amanda': {'location': 'Pacific', 'start': 570, 'end': 705, 'min': 90},
        'James': {'location': 'Alamo', 'start': 45, 'end': 735, 'min': 90},
        'Sarah': {'location': 'Fisherman', 'start': -60, 'end': 750, 'min': 90},
        'Melissa': {'location': 'Golden', 'start': 0, 'end': 585, 'min': 90}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at The Castro at 9:00 AM (time = 0)
    current_loc = 'Castro'
    
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
        current_loc = 'Castro'
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