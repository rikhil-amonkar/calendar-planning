from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = [
        'Embarcadero', 'Fisherman', 'Financial', 'Russian', 'Marina',
        'Richmond', 'Pacific', 'Haight', 'Presidio', 'Nob', 'Castro'
    ]
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 6, 5, 8, 12, 21, 11, 21, 20, 10, 25],    # Embarcadero
        [8, 0, 11, 7, 9, 18, 12, 22, 17, 11, 27],     # Fisherman
        [4, 10, 0, 11, 15, 21, 13, 19, 22, 8, 20],     # Financial
        [8, 7, 11, 0, 7, 14, 7, 17, 14, 5, 21],        # Russian
        [14, 10, 17, 8, 0, 11, 7, 16, 10, 12, 22],     # Marina
        [19, 18, 22, 13, 9, 0, 10, 10, 7, 17, 16],     # Richmond
        [10, 13, 13, 7, 6, 12, 0, 11, 11, 8, 16],      # Pacific
        [20, 23, 21, 17, 17, 10, 12, 0, 15, 15, 6],    # Haight
        [20, 19, 23, 14, 11, 7, 11, 15, 0, 18, 21],   # Presidio
        [9, 10, 9, 5, 11, 14, 8, 13, 17, 0, 17],       # Nob
        [22, 24, 21, 18, 21, 16, 16, 6, 20, 16, 0]    # Castro
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Stephanie': {'location': 'Fisherman', 'start': 390, 'end': 780, 'min': 30},
        'Lisa': {'location': 'Financial', 'start': 105, 'end': 495, 'min': 15},
        'Melissa': {'location': 'Russian', 'start': 480, 'end': 645, 'min': 120},
        'Betty': {'location': 'Marina', 'start': 105, 'end': 255, 'min': 60},
        'Sarah': {'location': 'Richmond', 'start': 435, 'end': 570, 'min': 105},
        'Daniel': {'location': 'Pacific', 'start': 570, 'end': 645, 'min': 60},
        'Joshua': {'location': 'Haight', 'start': 0, 'end': 390, 'min': 15},
        'Joseph': {'location': 'Presidio', 'start': -120, 'end': 240, 'min': 45},
        'Andrew': {'location': 'Nob', 'start': 645, 'end': 780, 'min': 105},
        'John': {'location': 'Castro', 'start': 255, 'end': 645, 'min': 45}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    met_friends = Int('met_friends')
    
    # Constraints
    current_time = 0  # Start at Embarcadero at 9:00 AM (time = 0)
    current_loc = 'Embarcadero'
    
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
        current_loc = 'Embarcadero'
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