from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = ['Haight', 'Fisherman', 'Richmond', 'Mission', 'Bayview']
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Time variables (in minutes since 9:00 AM)
    max_time = 780  # 9:00 AM to 10:00 PM is 13 hours = 780 minutes
    travel_times = [
        [0, 23, 10, 11, 18],    # From Haight
        [22, 0, 18, 22, 26],     # From Fisherman
        [10, 18, 0, 20, 26],     # From Richmond
        [12, 22, 20, 0, 15],     # From Mission
        [19, 25, 25, 13, 0]      # From Bayview
    ]
    
    # Friend availability
    friends = {
        'Sarah': {'location': 'Fisherman', 'start': 345, 'end': 450, 'min': 105},
        'Mary': {'location': 'Richmond', 'start': 240, 'end': 435, 'min': 75},
        'Helen': {'location': 'Mission', 'start': 585, 'end': 630, 'min': 30},
        'Thomas': {'location': 'Bayview', 'start': 375, 'end': 465, 'min': 120}
    }
    
    # Decision variables
    arrival = {f: Int(f'arrival_{f}') for f in friends}
    departure = {f: Int(f'departure_{f}') for f in friends}
    meet_time = {f: Int(f'meet_{f}') for f in friends}
    total_meet_time = Int('total_meet_time')
    
    # Constraints
    current_time = 0  # Start at Haight at 9:00 AM (time = 0)
    current_loc = 'Haight'
    
    for f in friends:
        # Arrival must be during friend's availability
        s.add(arrival[f] >= friends[f]['start'])
        s.add(arrival[f] <= friends[f]['end'])
        
        # Departure must be during friend's availability
        s.add(departure[f] >= friends[f]['start'])
        s.add(departure[f] <= friends[f]['end'])
        
        # Meeting duration
        s.add(meet_time[f] == departure[f] - arrival[f])
        s.add(meet_time[f] >= friends[f]['min'])
        
        # Travel time from current location
        travel = travel_times[n_indices[current_loc]][n_indices[friends[f]['location']]
        s.add(arrival[f] >= current_time + travel)
        
        # Update current time and location
        current_time = departure[f]
        current_loc = friends[f]['location']
    
    # Helen must be last (since she's available latest)
    s.add(departure['Helen'] == friends['Helen']['end'])
    
    # Total meeting time
    s.add(total_meet_time == sum(meet_time[f] for f in friends))
    
    # Maximize total meeting time
    s.maximize(total_meet_time)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        schedule = []
        for f in friends:
            start = m.eval(arrival[f]).as_long()
            end = m.eval(departure[f]).as_long()
            duration = m.eval(meet_time[f]).as_long()
            schedule.append((f, friends[f]['location'], start, end, duration))
        
        # Sort by start time
        schedule.sort(key=lambda x: x[2])
        
        print("OPTIMAL SCHEDULE:")
        for f, loc, start, end, duration in schedule:
            print(f"Meet {f} in {loc} from {minutes_to_time(start)} to {minutes_to_time(end)} ({duration} mins)")
        
        total = m.eval(total_meet_time).as_long()
        print(f"\nTotal meeting time: {total} minutes")
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