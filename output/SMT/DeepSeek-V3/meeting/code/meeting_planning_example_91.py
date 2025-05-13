from z3 import *

def optimize_schedule():
    # Initialize solver
    s = Optimize()

    # Neighborhoods
    neighborhoods = ['Russian', 'Richmond']
    n_indices = {n: idx for idx, n in enumerate(neighborhoods)}
    
    # Travel times matrix (minutes)
    travel_times = [
        [0, 14],    # Russian Hill
        [13, 0]      # Richmond District
    ]
    
    # Friend availability (in minutes since 9:00 AM)
    friends = {
        'Daniel': {'location': 'Richmond', 'start': 600, 'end': 615, 'min': 75}
    }
    
    # Decision variables
    arrival = Int('arrival_Daniel')
    departure = Int('departure_Daniel')
    meet_time = Int('meet_Daniel')
    
    # Constraints
    current_time = 0  # Start at Russian Hill at 9:00 AM (time = 0)
    current_loc = 'Russian'
    
    # Track whether we meet Daniel
    met = Bool('met_Daniel')
    
    # Can choose to meet or not meet Daniel
    s.add(Implies(met, arrival >= friends['Daniel']['start']))
    s.add(Implies(met, arrival <= friends['Daniel']['end']))
    s.add(Implies(met, departure >= friends['Daniel']['start']))
    s.add(Implies(met, departure <= friends['Daniel']['end']))
    s.add(Implies(met, meet_time == departure - arrival))
    s.add(Implies(met, meet_time >= friends['Daniel']['min']))
    s.add(Implies(Not(met), meet_time == 0))
    
    # Travel time from current location if we meet Daniel
    travel = travel_times[n_indices[current_loc]][n_indices[friends['Daniel']['location']]]
    s.add(Implies(met, arrival >= current_time + travel))
    
    # Optimization objective (meet Daniel)
    s.maximize(If(met, 1, 0))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        if m.eval(met):
            start = m.eval(arrival).as_long()
            end = m.eval(departure).as_long()
            duration = m.eval(meet_time).as_long()
            
            print("OPTIMAL SCHEDULE:")
            print(f"Travel from Russian Hill to Richmond District (14 mins)")
            print(f"Meet Daniel in Richmond District from {minutes_to_time(start)} to {minutes_to_time(end)} ({duration} mins)")
            print(f"\nTotal friends met: 1")
            print(f"Total meeting time: {duration} minutes")
        else:
            print("No valid schedule found - cannot meet Daniel within given constraints")
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