from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and their indices
    locations = {
        "Marina District": 0,
        "Richmond District": 1,
        "Union Square": 2,
        "Nob Hill": 3,
        "Fisherman's Wharf": 4,
        "Golden Gate Park": 5,
        "Embarcadero": 6,
        "Financial District": 7,
        "North Beach": 8,
        "Presidio": 9
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 11, 16, 12, 10, 18, 14, 17, 11, 10],  # Marina District
        [9, 0, 21, 17, 18, 9, 19, 22, 17, 7],     # Richmond District
        [18, 20, 0, 9, 15, 22, 11, 9, 10, 24],    # Union Square
        [11, 14, 7, 0, 10, 17, 9, 9, 8, 17],      # Nob Hill
        [9, 18, 13, 11, 0, 25, 8, 11, 6, 17],     # Fisherman's Wharf
        [16, 7, 22, 20, 24, 0, 25, 26, 23, 11],   # Golden Gate Park
        [12, 21, 10, 10, 6, 25, 0, 5, 5, 20],     # Embarcadero
        [15, 21, 9, 8, 10, 23, 4, 0, 7, 22],      # Financial District
        [9, 18, 7, 7, 5, 22, 6, 8, 0, 17],        # North Beach
        [11, 7, 22, 18, 19, 12, 20, 23, 18, 0]    # Presidio
    ]

    # Friends' data: name, location, start time, end time, min duration (in minutes)
    friends = [
        ("Stephanie", "Richmond District", 16*60 + 15, 21*60 + 30, 75),
        ("William", "Union Square", 10*60 + 45, 17*60 + 30, 45),
        ("Elizabeth", "Nob Hill", 12*60 + 15, 15*60 + 0, 105),
        ("Joseph", "Fisherman's Wharf", 12*60 + 45, 14*60 + 0, 75),
        ("Anthony", "Golden Gate Park", 13*60 + 0, 20*60 + 30, 75),
        ("Barbara", "Embarcadero", 19*60 + 15, 20*60 + 30, 75),
        ("Carol", "Financial District", 11*60 + 45, 16*60 + 15, 60),
        ("Sandra", "North Beach", 10*60 + 0, 12*60 + 30, 15),
        ("Kenneth", "Presidio", 21*60 + 15, 22*60 + 15, 45)
    ]

    # Current location starts at Marina District at 9:00 AM (540 minutes)
    current_location = locations["Marina District"]
    current_time = 9 * 60

    # Variables for each friend
    meet_vars = []
    for name, loc, friend_start, friend_end, min_duration in friends:
        met = Bool(f'met_{name}')
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meet_vars.append({
            'name': name,
            'loc': loc,
            'friend_start': friend_start,
            'friend_end': friend_end,
            'min_duration': min_duration,
            'met': met,
            'start': start,
            'end': end
        })
        
        # Constraints if met
        s.add(Implies(met, start >= friend_start))
        s.add(Implies(met, end <= friend_end))
        s.add(Implies(met, end == start + min_duration))
        # If not met, set start and end to 0
        s.add(Implies(Not(met), start == 0))
        s.add(Implies(Not(met), end == 0))

    # Exactly 8 friends must be met
    s.add(Sum([If(m['met'], 1, 0) for m in meet_vars]) == 8)

    # Create ordering variables
    order = [Int(f'order_{i}') for i in range(len(meet_vars))]
    s.add(Distinct(order))
    for i in range(len(order)):
        s.add(order[i] >= 0)
        s.add(order[i] < len(meet_vars))

    # Add travel time constraints between consecutive meetings
    for i in range(len(meet_vars)):
        for j in range(len(meet_vars)):
            if i != j:
                m1 = meet_vars[i]
                m2 = meet_vars[j]
                # If both are met and m2 comes after m1, add travel time
                s.add(Implies(And(m1['met'], m2['met'], order[i] < order[j]),
                             m2['start'] >= m1['end'] + travel_times[locations[m1['loc']]][locations[m2['loc']]]))

    # Initial travel from Marina District to first meeting
    for i in range(len(meet_vars)):
        m = meet_vars[i]
        s.add(Implies(And(m['met'], order[i] == 0),
                     m['start'] >= current_time + travel_times[current_location][locations[m['loc']]]))

    # Ensure no overlapping meetings
    for i in range(len(meet_vars)):
        for j in range(i + 1, len(meet_vars)):
            m1 = meet_vars[i]
            m2 = meet_vars[j]
            s.add(Implies(And(m1['met'], m2['met']), 
                         Or(m1['end'] <= m2['start'], m2['end'] <= m1['start'])))

    if s.check() == sat:
        m = s.model()
        schedule = []
        for idx, meeting in enumerate(meet_vars):
            if m.evaluate(meeting['met']):
                start_val = m.evaluate(meeting['start']).as_long()
                end_val = m.evaluate(meeting['end']).as_long()
                order_val = m.evaluate(order[idx]).as_long()
                schedule.append((order_val, meeting['name'], meeting['loc'], start_val, end_val))
        schedule.sort()
        return [x[1:] for x in schedule]
    else:
        return None

schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    print("Optimal Schedule (8 friends met):")
    for name, loc, start, end in schedule:
        start_hr = start // 60
        start_min = start % 60
        end_hr = end // 60
        end_min = end % 60
        print(f"Meet {name} at {loc} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
else:
    print("No feasible schedule found that meets exactly 8 friends.")