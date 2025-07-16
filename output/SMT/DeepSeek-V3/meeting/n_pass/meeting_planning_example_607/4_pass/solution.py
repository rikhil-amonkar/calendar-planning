from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define friends and their availability
    friends = [
        {'name': 'Karen', 'location': 'Russian Hill', 'start': 20.75, 'end': 21.75, 'min_duration': 1.0},
        {'name': 'Jessica', 'location': 'The Castro', 'start': 15.75, 'end': 19.5, 'min_duration': 1.0},
        {'name': 'Matthew', 'location': 'Richmond District', 'start': 7.5, 'end': 15.25, 'min_duration': 0.25},
        {'name': 'Michelle', 'location': 'Marina District', 'start': 10.5, 'end': 18.75, 'min_duration': 1.25},
        {'name': 'Carol', 'location': 'North Beach', 'start': 12.0, 'end': 17.0, 'min_duration': 1.5},
        {'name': 'Stephanie', 'location': 'Union Square', 'start': 10.75, 'end': 14.25, 'min_duration': 0.5},
        {'name': 'Linda', 'location': 'Golden Gate Park', 'start': 10.75, 'end': 22.0, 'min_duration': 1.5}
    ]

    # Travel times in hours (from -> to -> duration)
    travel_times = {
        ('Sunset District', 'Russian Hill'): 24/60,
        ('Sunset District', 'The Castro'): 17/60,
        ('Sunset District', 'Richmond District'): 12/60,
        ('Sunset District', 'Marina District'): 21/60,
        ('Sunset District', 'North Beach'): 29/60,
        ('Sunset District', 'Union Square'): 30/60,
        ('Sunset District', 'Golden Gate Park'): 11/60,
        ('Russian Hill', 'Sunset District'): 23/60,
        ('Russian Hill', 'The Castro'): 21/60,
        ('Russian Hill', 'Richmond District'): 14/60,
        ('Russian Hill', 'Marina District'): 7/60,
        ('Russian Hill', 'Marina District'): 7/60,
        ('Russian Hill', 'North Beach'): 5/60,
        ('Russian Hill', 'Union Square'): 11/60,
        ('Russian Hill', 'Golden Gate Park'): 21/60,
        ('The Castro', 'Sunset District'): 17/60,
        ('The Castro', 'Russian Hill'): 18/60,
        ('The Castro', 'Richmond District'): 16/60,
        ('The Castro', 'Marina District'): 21/60,
        ('The Castro', 'North Beach'): 20/60,
        ('The Castro', 'Union Square'): 19/60,
        ('The Castro', 'Golden Gate Park'): 11/60,
        ('Richmond District', 'Sunset District'): 11/60,
        ('Richmond District', 'Russian Hill'): 13/60,
        ('Richmond District', 'The Castro'): 16/60,
        ('Richmond District', 'Marina District'): 9/60,
        ('Richmond District', 'North Beach'): 17/60,
        ('Richmond District', 'Union Square'): 21/60,
        ('Richmond District', 'Golden Gate Park'): 9/60,
        ('Marina District', 'Sunset District'): 19/60,
        ('Marina District', 'Russian Hill'): 8/60,
        ('Marina District', 'The Castro'): 22/60,
        ('Marina District', 'Richmond District'): 11/60,
        ('Marina District', 'North Beach'): 11/60,
        ('Marina District', 'Union Square'): 16/60,
        ('Marina District', 'Golden Gate Park'): 18/60,
        ('North Beach', 'Sunset District'): 27/60,
        ('North Beach', 'Russian Hill'): 4/60,
        ('North Beach', 'The Castro'): 22/60,
        ('North Beach', 'Richmond District'): 18/60,
        ('North Beach', 'Marina District'): 9/60,
        ('North Beach', 'Union Square'): 7/60,
        ('North Beach', 'Golden Gate Park'): 22/60,
        ('Union Square', 'Sunset District'): 26/60,
        ('Union Square', 'Russian Hill'): 13/60,
        ('Union Square', 'The Castro'): 19/60,
        ('Union Square', 'Richmond District'): 20/60,
        ('Union Square', 'Marina District'): 18/60,
        ('Union Square', 'North Beach'): 10/60,
        ('Union Square', 'Golden Gate Park'): 22/60,
        ('Golden Gate Park', 'Sunset District'): 10/60,
        ('Golden Gate Park', 'Russian Hill'): 19/60,
        ('Golden Gate Park', 'The Castro'): 13/60,
        ('Golden Gate Park', 'Richmond District'): 7/60,
        ('Golden Gate Park', 'Marina District'): 16/60,
        ('Golden Gate Park', 'North Beach'): 24/60,
        ('Golden Gate Park', 'Union Square'): 22/60
    }

    # Create variables for each friend
    meet_vars = {f['name']: Bool(f"meet_{f['name']}") for f in friends}
    start_vars = {f['name']: Real(f"start_{f['name']}") for f in friends}
    end_vars = {f['name']: Real(f"end_{f['name']}") for f in friends}

    # Current time and location
    current_time = 9.0  # Starting at 9:00 AM
    current_location = 'Sunset District'

    # We must meet Karen
    s.add(meet_vars['Karen'] == True)

    # For each friend, add constraints if we meet them
    for f in friends:
        name = f['name']
        loc = f['location']
        min_dur = f['min_duration']
        avail_start = f['start']
        avail_end = f['end']

        # If we meet this friend, their meeting must fit in their window
        s.add(Implies(meet_vars[name],
                     And(start_vars[name] >= avail_start,
                         end_vars[name] <= avail_end,
                         end_vars[name] == start_vars[name] + min_dur)))

        # Travel time from current location to friend's location
        travel_time = Real(f"travel_{name}")
        s.add(travel_time == travel_times.get((current_location, loc), 0))

        # Meeting must start after arriving (accounting for travel time)
        s.add(Implies(meet_vars[name],
                     start_vars[name] >= current_time + travel_time))

        # Update current time and location if we meet this friend
        new_time = Real(f"new_time_{name}")
        new_loc = String(f"new_loc_{name}")
        s.add(new_time == If(meet_vars[name], end_vars[name], current_time))
        s.add(new_loc == If(meet_vars[name], loc, current_location))

        current_time = new_time
        current_location = new_loc

    # Maximize the number of friends met
    total_met = Int('total_met')
    s.add(total_met == Sum([If(meet_vars[f['name']], 1, 0) for f in friends]))
    s.maximize(total_met)

    # Check if solution exists
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        
        # Collect all meetings
        meetings = []
        for f in friends:
            if m.evaluate(meet_vars[f['name']]):
                start = m.evaluate(start_vars[f['name']])
                end = m.evaluate(end_vars[f['name']])
                meetings.append({
                    'name': f['name'],
                    'location': f['location'],
                    'start': start,
                    'end': end,
                    'duration': f['min_duration']
                })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: float(str(x['start'])))
        
        # Print schedule
        for meeting in meetings:
            start = float(str(meeting['start']))
            end = float(str(meeting['end']))
            start_hr = int(start)
            start_min = int((start - start_hr) * 60)
            end_hr = int(end)
            end_min = int((end - end_hr) * 60)
            print(f"Meet {meeting['name']} at {meeting['location']} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d} (Duration: {meeting['duration']*60:.0f} min)")
        
        print(f"\nTotal friends met: {len(meetings)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()