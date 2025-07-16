from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()
    
    # Locations and their indices
    locations = {
        'Union Square': 0,
        'The Castro': 1,
        'North Beach': 2,
        'Embarcadero': 3,
        'Alamo Square': 4,
        'Nob Hill': 5,
        'Presidio': 6,
        'Fisherman\'s Wharf': 7,
        'Mission District': 8,
        'Haight-Ashbury': 9
    }
    
    # Travel times matrix (from_location_index, to_location_index) -> minutes
    travel_times = [
        [0, 17, 10, 11, 15, 9, 24, 15, 14, 18],  # Union Square
        [19, 0, 20, 22, 8, 16, 20, 24, 7, 6],     # The Castro
        [7, 23, 0, 6, 16, 7, 17, 5, 18, 18],      # North Beach
        [10, 25, 5, 0, 19, 10, 20, 6, 20, 21],    # Embarcadero
        [14, 8, 15, 16, 0, 11, 17, 19, 10, 5],    # Alamo Square
        [7, 17, 8, 9, 11, 0, 17, 10, 13, 13],    # Nob Hill
        [22, 21, 18, 20, 19, 18, 0, 19, 26, 15],  # Presidio
        [13, 27, 6, 8, 21, 11, 17, 0, 22, 22],    # Fisherman's Wharf
        [15, 7, 17, 19, 11, 12, 25, 22, 0, 12],   # Mission District
        [19, 6, 19, 20, 5, 15, 15, 23, 11, 0]     # Haight-Ashbury
    ]
    
    # Friends data: name, location, start_time, end_time, min_duration
    friends = [
        ('Melissa', 'The Castro', (20, 15), (21, 15), 30),
        ('Kimberly', 'North Beach', (7, 0), (10, 30), 15),
        ('Joseph', 'Embarcadero', (15, 30), (19, 30), 75),
        ('Barbara', 'Alamo Square', (20, 45), (21, 45), 15),
        ('Kenneth', 'Nob Hill', (12, 15), (17, 15), 105),
        ('Joshua', 'Presidio', (16, 30), (18, 15), 105),
        ('Brian', 'Fisherman\'s Wharf', (9, 30), (15, 30), 45),
        ('Steven', 'Mission District', (19, 30), (21, 0), 90),
        ('Betty', 'Haight-Ashbury', (19, 0), (20, 30), 90)
    ]
    
    # Convert time to minutes since midnight
    def time_to_minutes(h, m):
        return h * 60 + m
    
    # Current location is Union Square at 9:00 AM (540 minutes)
    initial_time = time_to_minutes(9, 0)
    current_location = locations['Union Square']
    
    # Variables for each friend: start, end, and whether they are met
    friend_vars = []
    for name, loc, (sh, sm), (eh, em), min_dur in friends:
        start_min = time_to_minutes(sh, sm)
        end_min = time_to_minutes(eh, em)
        loc_idx = locations[loc]
        
        start = Int(f'start_{name.replace(" ", "_")}')
        end = Int(f'end_{name.replace(" ", "_")}')
        met = Bool(f'met_{name.replace(" ", "_")}')
        
        # Constraints for time window and duration
        s.add(Implies(met, start >= start_min))
        s.add(Implies(met, end <= end_min))
        s.add(Implies(met, end == start + min_dur))
        
        friend_vars.append((name, loc_idx, start, end, met))
    
    # Sequence constraints: meetings must be scheduled in order with travel times
    # We'll create an order variable for each meeting to determine the sequence
    order = [Int(f'order_{name.replace(" ", "_")}') for name, _, _, _, _ in friend_vars]
    s.add(Distinct(order))
    for i in range(len(order)):
        s.add(order[i] >= 0)
        s.add(order[i] < len(order))
    
    # For each pair of meetings, if one comes after another, enforce travel time
    for i in range(len(friend_vars)):
        for j in range(len(friend_vars)):
            if i == j:
                continue
            name_i, loc_i, start_i, end_i, met_i = friend_vars[i]
            name_j, loc_j, start_j, end_j, met_j = friend_vars[j]
            s.add(Implies(And(met_i, met_j, order[i] < order[j]),
                          start_j >= end_i + travel_times[loc_i][loc_j]))
    
    # The first meeting must start after initial_time + travel from Union Square to its location
    for i in range(len(friend_vars)):
        name, loc, start, end, met = friend_vars[i]
        s.add(Implies(And(met, order[i] == 0),
                      start >= initial_time + travel_times[current_location][loc]))
    
    # Maximize the number of friends met
    total_met = Sum([If(met, 1, 0) for (_, _, _, _, met) in friend_vars])
    s.maximize(total_met)
    
    # Solve
    if s.check() == sat:
        model = s.model()
        scheduled_meetings = []
        for (name, loc_idx, start, end, met) in friend_vars:
            if is_true(model[met]):
                start_val = model[start].as_long()
                end_val = model[end].as_long()
                loc = [k for k, v in locations.items() if v == loc_idx][0]
                scheduled_meetings.append((name, loc, start_val, end_val))
        
        # Sort by start time
        scheduled_meetings.sort(key=lambda x: x[2])
        
        print("Optimal Schedule:")
        for meeting in scheduled_meetings:
            name, loc, start, end = meeting
            print(f"Meet {name} at {loc} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
        print(f"Total friends met: {len(scheduled_meetings)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()