from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

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

    # Variables for each meeting: start time, end time, and whether the meeting is scheduled
    meeting_vars = []
    for i, (name, loc, avail_start, avail_end, min_dur) in enumerate(friends):
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        scheduled = Bool(f'scheduled_{name}')
        meeting_vars.append((name, loc, avail_start, avail_end, min_dur, start, end, scheduled))

    # Current time starts at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes

    # Constraints for each meeting
    order = []  # To keep track of the order of meetings
    prev_end = current_time
    prev_loc = locations['Financial District']

    # To maximize the number of friends met, we'll allow the solver to choose which meetings to attend
    for name, loc, avail_start, avail_end, min_dur, start, end, scheduled in meeting_vars:
        loc_idx = locations[loc]

        # If the meeting is scheduled, it must fit within the availability window and meet duration
        s.add(Implies(scheduled, start >= avail_start))
        s.add(Implies(scheduled, end <= avail_end))
        s.add(Implies(scheduled, end == start + min_dur))

        # Travel time from previous location to current meeting location
        travel_time = travel_times[prev_loc][loc_idx]
        s.add(Implies(scheduled, start >= prev_end + travel_time))

        # Update previous end and location if this meeting is scheduled
        new_prev_end = If(scheduled, end, prev_end)
        new_prev_loc = If(scheduled, loc_idx, prev_loc)
        prev_end = new_prev_end
        prev_loc = new_prev_loc

        order.append(scheduled)

    # Maximize the number of scheduled meetings
    num_scheduled = Sum([If(scheduled, 1, 0) for _, _, _, _, _, _, _, scheduled in meeting_vars])
    s.maximize(num_scheduled)

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        scheduled_meetings = []
        for name, loc, avail_start, avail_end, min_dur, start, end, scheduled in meeting_vars:
            if is_true(m.eval(scheduled)):
                start_val = m.eval(start).as_long()
                end_val = m.eval(end).as_long()
                scheduled_meetings.append((
                    name,
                    loc,
                    f"{start_val // 60}:{start_val % 60:02d}",
                    f"{end_val // 60}:{end_val % 60:02d}"
                ))
        # Sort by start time
        scheduled_meetings.sort(key=lambda x: x[2])
        return scheduled_meetings
    else:
        return None

# Solve and print the schedule
schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    print("Optimal schedule to meet the most friends:")
    for name, loc, start, end in schedule:
        print(f"Meet {name} at {loc} from {start} to {end}")
else:
    print("No feasible schedule found.")