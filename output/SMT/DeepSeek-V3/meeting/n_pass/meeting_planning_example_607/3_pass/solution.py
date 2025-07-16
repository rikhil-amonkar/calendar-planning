from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define the friends and their details
    friends = {
        'Karen': {'location': 'Russian Hill', 'start': 20.75, 'end': 21.75, 'min_duration': 1.0},
        'Jessica': {'location': 'The Castro', 'start': 15.75, 'end': 19.5, 'min_duration': 1.0},
        'Matthew': {'location': 'Richmond District', 'start': 7.5, 'end': 15.25, 'min_duration': 0.25},
        'Michelle': {'location': 'Marina District', 'start': 10.5, 'end': 18.75, 'min_duration': 1.25},
        'Carol': {'location': 'North Beach', 'start': 12.0, 'end': 17.0, 'min_duration': 1.5},
        'Stephanie': {'location': 'Union Square', 'start': 10.75, 'end': 14.25, 'min_duration': 0.5},
        'Linda': {'location': 'Golden Gate Park', 'start': 10.75, 'end': 22.0, 'min_duration': 1.5}
    }

    # Travel times dictionary (from -> to -> minutes converted to hours)
    travel_times = {
        'Sunset District': {
            'Russian Hill': 24/60,
            'The Castro': 17/60,
            'Richmond District': 12/60,
            'Marina District': 21/60,
            'North Beach': 29/60,
            'Union Square': 30/60,
            'Golden Gate Park': 11/60
        },
        'Russian Hill': {
            'Sunset District': 23/60,
            'The Castro': 21/60,
            'Richmond District': 14/60,
            'Marina District': 7/60,
            'Marina District': 7/60,
            'North Beach': 5/60,
            'Union Square': 11/60,
            'Golden Gate Park': 21/60
        },
        'The Castro': {
            'Sunset District': 17/60,
            'Russian Hill': 18/60,
            'Richmond District': 16/60,
            'Marina District': 21/60,
            'North Beach': 20/60,
            'Union Square': 19/60,
            'Golden Gate Park': 11/60
        },
        'Richmond District': {
            'Sunset District': 11/60,
            'Russian Hill': 13/60,
            'The Castro': 16/60,
            'Marina District': 9/60,
            'North Beach': 17/60,
            'Union Square': 21/60,
            'Golden Gate Park': 9/60
        },
        'Marina District': {
            'Sunset District': 19/60,
            'Russian Hill': 8/60,
            'The Castro': 22/60,
            'Richmond District': 11/60,
            'North Beach': 11/60,
            'Union Square': 16/60,
            'Golden Gate Park': 18/60
        },
        'North Beach': {
            'Sunset District': 27/60,
            'Russian Hill': 4/60,
            'The Castro': 22/60,
            'Richmond District': 18/60,
            'Marina District': 9/60,
            'Union Square': 7/60,
            'Golden Gate Park': 22/60
        },
        'Union Square': {
            'Sunset District': 26/60,
            'Russian Hill': 13/60,
            'The Castro': 19/60,
            'Richmond District': 20/60,
            'Marina District': 18/60,
            'North Beach': 10/60,
            'Golden Gate Park': 22/60
        },
        'Golden Gate Park': {
            'Sunset District': 10/60,
            'Russian Hill': 19/60,
            'The Castro': 13/60,
            'Richmond District': 7/60,
            'Marina District': 16/60,
            'North Beach': 24/60,
            'Union Square': 22/60
        }
    }

    # Create variables for each friend's meeting start and end times
    meeting_starts = {name: Real(f'start_{name}') for name in friends}
    meeting_ends = {name: Real(f'end_{name}') for name in friends}
    meet = {name: Bool(f'meet_{name}') for name in friends}  # Whether we meet this friend

    # Current location starts at Sunset District at 9:00 AM (9.0)
    current_time = 9.0
    current_location = 'Sunset District'

    # To keep track of the last meeting's end time and location
    last_end = Real('last_end')
    last_location = String('last_location')
    s.add(last_end == current_time)
    s.add(last_location == current_location)

    # For each friend, add constraints if we choose to meet them
    for name in friends:
        friend = friends[name]
        loc = friend['location']
        min_dur = friend['min_duration']
        avail_start = friend['start']
        avail_end = friend['end']

        # If we meet this friend, their meeting must fit in their window and meet duration
        s.add(Implies(meet[name], And(
            meeting_starts[name] >= avail_start,
            meeting_ends[name] <= avail_end,
            meeting_ends[name] == meeting_starts[name] + min_dur
        )))

        # Also, the meeting must start after arriving at their location (travel time from last location)
        travel_time = Real(f'travel_{name}')
        from_loc = last_location
        to_loc = loc
        # Handle travel time: if from_loc and to_loc are the same, travel time is 0
        s.add(If(from_loc == to_loc, travel_time == 0, 
                travel_time == travel_times[from_loc][to_loc]))

        s.add(Implies(meet[name], 
                     meeting_starts[name] >= last_end + travel_time))

        # Update last_end and last_location if we meet this friend
        new_last_end = Real(f'new_last_end_{name}')
        new_last_location = String(f'new_last_location_{name}')
        s.add(new_last_end == If(meet[name], meeting_ends[name], last_end))
        s.add(new_last_location == If(meet[name], to_loc, last_location))

        last_end = new_last_end
        last_location = new_last_location

    # We must meet Karen (since she's only available late)
    s.add(meet['Karen'] == True)

    # Maximize the number of friends met
    # To do this, we'll optimize the sum of meet variables (1 if met, 0 otherwise)
    total_met = Int('total_met')
    s.add(total_met == Sum([If(meet[name], 1, 0) for name in friends]))
    maximize_total_met = Int('maximize_total_met')
    s.add(maximize_total_met == total_met)
    s.maximize(maximize_total_met)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        scheduled = []
        for name in friends:
            if m.evaluate(meet[name]):
                start = m.evaluate(meeting_starts[name])
                end = m.evaluate(meeting_ends[name])
                duration = float(end.as_fraction()) - float(start.as_fraction())
                scheduled.append((name, float(start.as_fraction()), float(end.as_fraction()), duration))
        scheduled.sort(key=lambda x: x[1])  # Sort by start time

        for name, start, end, duration in scheduled:
            start_hr = int(start)
            start_min = int((start - start_hr) * 60)
            end_hr = int(end)
            end_min = int((end - end_hr) * 60)
            print(f"Meet {name} at {friends[name]['location']} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d} (Duration: {duration*60:.0f} minutes)")

        total_friends_met = sum(1 for name in friends if m.evaluate(meet[name]))
        print(f"\nTotal friends met: {total_friends_met}")
    else:
        print("No feasible schedule found.")

solve_scheduling()