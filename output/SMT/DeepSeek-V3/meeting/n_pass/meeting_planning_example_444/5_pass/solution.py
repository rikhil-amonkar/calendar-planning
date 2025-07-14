from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Locations mapping
    locations = {
        'Financial District': 0,
        'Russian Hill': 1,
        'Sunset District': 2,
        'North Beach': 3,
        'The Castro': 4,
        'Golden Gate Park': 5
    }

    # Travel times matrix (minutes)
    travel = [
        [0, 10, 31, 7, 23, 23],
        [11, 0, 23, 5, 21, 21],
        [30, 24, 0, 29, 17, 11],
        [8, 4, 27, 0, 22, 22],
        [20, 18, 17, 20, 0, 11],
        [26, 19, 10, 24, 13, 0]
    ]

    # Friends' availability
    friends = [
        ('Ronald', 'Russian Hill', 825, 1035, 105),  # 1:45PM-5:15PM
        ('Patricia', 'Sunset District', 555, 1320, 60),  # 9:15AM-10:00PM
        ('Laura', 'North Beach', 750, 765, 15),  # 12:30PM-12:45PM
        ('Emily', 'The Castro', 975, 1110, 60),  # 4:15PM-6:30PM
        ('Mary', 'Golden Gate Park', 900, 990, 60)  # 3:00PM-4:30PM
    ]

    # Create variables
    vars = []
    for name, loc, start_avail, end_avail, dur in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        scheduled = Bool(f'sched_{name}')
        vars.append((name, loc, start_avail, end_avail, dur, start, end, scheduled))

    # Starting point
    current_time = 540  # 9:00 AM
    current_loc = locations['Financial District']

    # Add constraints
    for name, loc, start_avail, end_avail, dur, start, end, scheduled in vars:
        loc_idx = locations[loc]
        
        # If scheduled, must be within availability window
        s.add(Implies(scheduled, And(
            start >= start_avail,
            end <= end_avail,
            end == start + dur
        )))
        
        # Travel time constraint
        s.add(Implies(scheduled, start >= current_time + travel[current_loc][loc_idx]))
        
        # Update current time and location if scheduled
        current_time = If(scheduled, end, current_time)
        current_loc = If(scheduled, loc_idx, current_loc)

    # Maximize number of scheduled meetings
    s.maximize(Sum([If(scheduled, 1, 0) for _, _, _, _, _, _, _, scheduled in vars]))

    # Solve and print results
    if s.check() == sat:
        m = s.model()
        results = []
        for name, loc, _, _, _, start, end, scheduled in vars:
            if is_true(m.eval(scheduled)):
                s_val = m.eval(start).as_long()
                e_val = m.eval(end).as_long()
                results.append((
                    s_val,
                    f"Meet {name} at {loc} from {s_val//60}:{s_val%60:02d} to {e_val//60}:{e_val%60:02d}"
                ))
        
        # Sort and print
        results.sort()
        print("SOLUTION:")
        for _, meeting in results:
            print(meeting)
    else:
        print("No feasible schedule found.")

solve_scheduling()