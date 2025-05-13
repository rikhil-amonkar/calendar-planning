from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Fisherman', 'Castro', 'Golden', 'Embarcadero', 
        'Russian', 'Nob', 'Alamo', 'North'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 26, 25, 8, 7, 11, 20, 6],      # Fisherman
        [24, 0, 11, 22, 18, 16, 8, 20],     # Castro
        [24, 13, 0, 25, 19, 20, 10, 22],    # Golden
        [6, 25, 25, 0, 8, 10, 19, 5],       # Embarcadero
        [7, 21, 21, 8, 0, 5, 15, 5],        # Russian
        [11, 17, 17, 9, 5, 0, 11, 8],       # Nob
        [19, 8, 9, 17, 13, 11, 0, 16],      # Alamo
        [5, 22, 22, 6, 4, 7, 16, 0]         # North
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Laura': {'location': 'Castro', 'start': 1065, 'end': 1170, 'min': 105},
        'Daniel': {'location': 'Golden', 'start': 1095, 'end': 1125, 'min': 15},
        'William': {'location': 'Embarcadero', 'start': -120, 'end': 0, 'min': 90},
        'Karen': {'location': 'Russian', 'start': 330, 'end': 525, 'min': 30},
        'Stephanie': {'location': 'Nob', 'start': -30, 'end': 90, 'min': 45},
        'Joseph': {'location': 'Alamo', 'start': 150, 'end': 225, 'min': 15},
        'Kimberly': {'location': 'North', 'start': 405, 'end': 555, 'min': 30}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Fisherman at 9:00 AM (time = 0)
    current_loc = 'Fisherman'
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
        current_loc = 'Fisherman'
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