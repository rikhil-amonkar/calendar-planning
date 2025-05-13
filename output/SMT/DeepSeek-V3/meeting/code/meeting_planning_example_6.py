from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = ['Fisherman', 'Nob']
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 11],    # Fisherman's Wharf
        [11, 0]      # Nob Hill
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Kenneth': {'location': 'Nob', 'start': 315, 'end': 465, 'min': 90}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    
    # Constraints
    current_time = 0  # Start at Fisherman's Wharf at 9:00 AM (time = 0)
    current_loc = 'Fisherman'
    
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
    
    # Optimization objective (meet the friend)
    s.maximize(If(met['Kenneth'], 1, 0))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        if m.eval(met['Kenneth']):
            start = m.eval(arrival['Kenneth']).as_long()
            end = m.eval(departure['Kenneth']).as_long()
            duration = m.eval(meet_time['Kenneth']).as_long()
            
            print("OPTIMAL SCHEDULE:")
            print(f"Travel from Fisherman's Wharf to Nob Hill (11 mins)")
            print(f"Meet Kenneth in Nob Hill from {minutes_to_time(start)} to {minutes_to_time(end)} ({duration} mins)")
            print(f"\nTotal friends met: 1")
            print(f"Total meeting time: {duration} minutes")
        else:
            print("No valid schedule found")
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