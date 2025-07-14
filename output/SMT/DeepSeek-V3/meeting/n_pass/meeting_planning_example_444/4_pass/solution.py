from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Locations and their indices
    locations = {
        'Financial District': 0,
        'Russian Hill': 1,
        'Sunset District': 2,
        'North Beach': 3,
        'The Castro': 4,
        'Golden Gate Park': 5
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 10, 31, 7, 23, 23],    # Financial District to others
        [11, 0, 23, 5, 21, 21],     # Russian Hill to others
        [30, 24, 0, 29, 17, 11],    # Sunset District to others
        [8, 4, 27, 0, 22, 22],      # North Beach to others
        [20, 18, 17, 20, 0, 11],    # The Castro to others
        [26, 19, 10, 24, 13, 0]     # Golden Gate Park to others
    ]

    # Friends' data: name, location, available start, available end, min duration (in minutes)
    friends = [
        ('Ronald', 'Russian Hill', 13*60 + 45, 17*60 + 15, 105),
        ('Patricia', 'Sunset District', 9*60 + 15, 22*60 + 0, 60),
        ('Laura', 'North Beach', 12*60 + 30, 12*60 + 45, 15),
        ('Emily', 'The Castro', 16*60 + 15, 18*60 + 30, 60),
        ('Mary', 'Golden Gate Park', 15*60 + 0, 16*60 + 30, 60)
    ]

    # Variables for each meeting
    meeting_vars = []
    for name, loc, avail_start, avail_end, min_dur in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        scheduled = Bool(f'scheduled_{name}')
        meeting_vars.append((name, loc, avail_start, avail_end, min_dur, start, end, scheduled))

    # Current time starts at 9:00 AM (540 minutes)
    current_time = 540
    prev_end = current_time
    prev_loc = locations['Financial District']

    # Constraints
    for name, loc, avail_start, avail_end, min_dur, start, end, scheduled in meeting_vars:
        loc_idx = locations[loc]
        
        # Meeting must be within availability window if scheduled
        s.add(Implies(scheduled, And(start >= avail_start, end <= avail_end, end == start + min_dur)))
        
        # Travel time constraint
        travel_time = travel_times[prev_loc][loc_idx]
        s.add(Implies(scheduled, start >= prev_end + travel_time))
        
        # Update previous end and location
        prev_end = If(scheduled, end, prev_end)
        prev_loc = If(scheduled, loc_idx, prev_loc)

    # Maximize number of scheduled meetings
    num_scheduled = Sum([If(scheduled, 1, 0) for _, _, _, _, _, _, _, scheduled in meeting_vars])
    s.maximize(num_scheduled)

    # Solve
    if s.check() == sat:
        m = s.model()
        scheduled_meetings = []
        for name, loc, _, _, _, start, end, scheduled in meeting_vars:
            if is_true(m.eval(scheduled)):
                start_val = m.eval(start).as_long()
                end_val = m.eval(end).as_long()
                start_str = f"{start_val//60:02d}:{start_val%60:02d}"
                end_str = f"{end_val//60:02d}:{end_val%60:02d}"
                scheduled_meetings.append((start_val, name, loc, start_str, end_str))
        
        # Sort by start time
        scheduled_meetings.sort()
        print("SOLUTION:")
        print("Optimal schedule to meet the most friends:")
        for _, name, loc, start, end in scheduled_meetings:
            print(f"Meet {name} at {loc} from {start} to {end}")
    else:
        print("No feasible schedule found.")

# Run the solver
solve_scheduling()