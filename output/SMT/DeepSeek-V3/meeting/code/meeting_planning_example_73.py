from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = ['Russian', 'Pacific']
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 7],    # Russian
        [7, 0]      # Pacific
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Barbara': {'location': 'Pacific', 'start': -105, 'end': 780, 'min': 60}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    
    # Constraints
    current_time = 0  # Start at Russian at 9:00 AM (time = 0)
    current_loc = 'Russian'
    
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
    met_friends = Sum([If(met[f], 1, 0) for f in friends])
    
    # Optimization objectives (maximize meeting time)
    s.maximize(met_friends * 1000 + Sum([meet_time[f] for f in friends]))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        print("OPTIMAL SCHEDULE:")
        current_loc = 'Russian'
        current_time = 0
        
        for f in friends:
            if m.eval(met[f]):
                start = m.eval(arrival[f]).as_long()
                end = m.eval(departure[f]).as_long()
                duration = m.eval(meet_time[f]).as_long()
                travel = travel_times[n_indices[current_loc]][n_indices[friends[f]['location']]]
                print(f"Travel from {current_loc} to {friends[f]['location']} ({travel} mins)")
                print(f"Meet {f} in {friends[f]['location']} from {minutes_to_time(start)} to {minutes_to_time(end)} ({duration} mins)")
                current_loc = friends[f]['location']
                current_time = end
        
        print(f"\nTotal friends met: {m.eval(met_friends)}")
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