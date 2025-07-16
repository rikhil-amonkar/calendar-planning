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

    # Travel times in minutes converted to hours
    travel_times = {
        ('Sunset District', 'Russian Hill'): 24/60,
        ('Sunset District', 'The Castro'): 17/60,
        ('Sunset District', 'Richmond District'): 12/60,
        ('Sunset District', 'Marina District'): 21/60,
        ('Sunset District', 'North Beach'): 29/60,
        ('Sunset District', 'Union Square'): 30/60,
        ('Sunset District', 'Golden Gate Park'): 11/60,
        ('Russian Hill', 'The Castro'): 21/60,
        ('Russian Hill', 'Richmond District'): 14/60,
        ('Russian Hill', 'Marina District'): 7/60,
        ('Russian Hill', 'North Beach'): 5/60,
        ('Russian Hill', 'Union Square'): 11/60,
        ('Russian Hill', 'Golden Gate Park'): 21/60,
        ('The Castro', 'Richmond District'): 16/60,
        ('The Castro', 'Marina District'): 21/60,
        ('The Castro', 'North Beach'): 20/60,
        ('The Castro', 'Union Square'): 19/60,
        ('The Castro', 'Golden Gate Park'): 11/60,
        ('Richmond District', 'Marina District'): 9/60,
        ('Richmond District', 'North Beach'): 17/60,
        ('Richmond District', 'Union Square'): 21/60,
        ('Richmond District', 'Golden Gate Park'): 9/60,
        ('Marina District', 'North Beach'): 11/60,
        ('Marina District', 'Union Square'): 16/60,
        ('Marina District', 'Golden Gate Park'): 18/60,
        ('North Beach', 'Union Square'): 7/60,
        ('North Beach', 'Golden Gate Park'): 22/60,
        ('Union Square', 'Golden Gate Park'): 22/60
    }

    # Create variables for each friend
    meet_vars = {f['name']: Bool(f"meet_{f['name']}") for f in friends}
    start_vars = {f['name']: Real(f"start_{f['name']}") for f in friends}
    end_vars = {f['name']: Real(f"end_{f['name']}") for f in friends}

    # Starting point
    current_time = 9.0  # 9:00 AM
    current_location = 'Sunset District'

    # We must meet Karen
    s.add(meet_vars['Karen'] == True)

    # For each friend, add constraints
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
            if is_true(m.evaluate(meet_vars[f['name']])):
                start = m.evaluate(start_vars[f['name']])
                end = m.evaluate(end_vars[f['name']])
                
                # Convert Z3 values to float
                start_val = float(str(start))
                end_val = float(str(end))
                
                meetings.append({
                    'name': f['name'],
                    'location': f['location'],
                    'start': start_val,
                    'end': end_val,
                    'duration': f['min_duration']
                })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x['start'])
        
        # Print schedule
        for meeting in meetings:
            start = meeting['start']
            end = meeting['end']
            start_hr = int(start)
            start_min = int((start - start_hr) * 60)
            end_hr = int(end)
            end_min = int((end - end_hr) * 60)
            print(f"Meet {meeting['name']} at {meeting['location']} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d} (Duration: {meeting['duration']*60:.0f} min)")
        
        print(f"\nTotal friends met: {len(meetings)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()