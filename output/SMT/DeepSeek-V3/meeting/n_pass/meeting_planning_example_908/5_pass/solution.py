from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friends and their details
    friends = {
        'Mark': {
            'location': 'Fisherman\'s Wharf',
            'start_window': 8.25,  # 8:15 AM
            'end_window': 10.0,    # 10:00 AM
            'min_duration': 0.5,   # 30 minutes
        },
        'Stephanie': {
            'location': 'Presidio',
            'start_window': 12.25,  # 12:15 PM
            'end_window': 15.0,    # 3:00 PM
            'min_duration': 1.25,  # 75 minutes
        },
        'Betty': {
            'location': 'Bayview',
            'start_window': 7.25,   # 7:15 AM
            'end_window': 20.5,     # 8:30 PM
            'min_duration': 0.25,   # 15 minutes
        },
        'Lisa': {
            'location': 'Haight-Ashbury',
            'start_window': 15.5,   # 3:30 PM
            'end_window': 18.5,     # 6:30 PM
            'min_duration': 0.75,   # 45 minutes
        },
        'William': {
            'location': 'Russian Hill',
            'start_window': 18.75, # 6:45 PM
            'end_window': 20.0,     # 8:00 PM
            'min_duration': 1.0,    # 60 minutes
        },
        'Brian': {
            'location': 'The Castro',
            'start_window': 9.25,   # 9:15 AM
            'end_window': 13.25,    # 1:15 PM
            'min_duration': 0.5,    # 30 minutes
        },
        'Joseph': {
            'location': 'Marina District',
            'start_window': 10.75,  # 10:45 AM
            'end_window': 15.0,     # 3:00 PM
            'min_duration': 1.5,    # 90 minutes
        },
        'Ashley': {
            'location': 'Richmond District',
            'start_window': 9.75,   # 9:45 AM
            'end_window': 11.25,    # 11:15 AM
            'min_duration': 0.75,   # 45 minutes
        },
        'Patricia': {
            'location': 'Union Square',
            'start_window': 16.5,  # 4:30 PM
            'end_window': 20.0,     # 8:00 PM
            'min_duration': 2.0,     # 120 minutes
        },
        'Karen': {
            'location': 'Sunset District',
            'start_window': 16.5,  # 4:30 PM
            'end_window': 22.0,     # 10:00 PM
            'min_duration': 1.75,   # 105 minutes
        }
    }

    # Travel times dictionary (from -> to -> hours)
    travel_times = {
        'Financial District': {
            'Fisherman\'s Wharf': 10/60,
            'Presidio': 22/60,
            'Bayview': 19/60,
            'Haight-Ashbury': 19/60,
            'Russian Hill': 11/60,
            'The Castro': 20/60,
            'Marina District': 15/60,
            'Richmond District': 21/60,
            'Union Square': 9/60,
            'Sunset District': 30/60,
        },
        'Fisherman\'s Wharf': {
            'Financial District': 11/60,
            'Presidio': 17/60,
            'Bayview': 26/60,
            'Haight-Ashbury': 22/60,
            'Russian Hill': 7/60,
            'The Castro': 27/60,
            'Marina District': 9/60,
            'Richmond District': 18/60,
            'Union Square': 13/60,
            'Sunset District': 27/60,
        },
        'Presidio': {
            'Financial District': 23/60,
            'Fisherman\'s Wharf': 19/60,
            'Bayview': 31/60,
            'Haight-Ashbury': 15/60,
            'Russian Hill': 14/60,
            'The Castro': 21/60,
            'Marina District': 11/60,
            'Richmond District': 7/60,
            'Union Square': 22/60,
            'Sunset District': 15/60,
        },
        'Bayview': {
            'Financial District': 19/60,
            'Fisherman\'s Wharf': 25/60,
            'Presidio': 32/60,
            'Haight-Ashbury': 19/60,
            'Russian Hill': 23/60,
            'The Castro': 19/60,
            'Marina District': 27/60,
            'Richmond District': 25/60,
            'Union Square': 18/60,
            'Sunset District': 23/60,
        },
        'Haight-Ashbury': {
            'Financial District': 21/60,
            'Fisherman\'s Wharf': 23/60,
            'Presidio': 15/60,
            'Bayview': 18/60,
            'Russian Hill': 17/60,
            'The Castro': 6/60,
            'Marina District': 17/60,
            'Richmond District': 10/60,
            'Union Square': 19/60,
            'Sunset District': 15/60,
        },
        'Russian Hill': {
            'Financial District': 11/60,
            'Fisherman\'s Wharf': 7/60,
            'Presidio': 14/60,
            'Bayview': 23/60,
            'Haight-Ashbury': 17/60,
            'The Castro': 21/60,
            'Marina District': 7/60,
            'Richmond District': 14/60,
            'Union Square': 10/60,
            'Sunset District': 23/60,
        },
        'The Castro': {
            'Financial District': 21/60,
            'Fisherman\'s Wharf': 24/60,
            'Presidio': 20/60,
            'Bayview': 19/60,
            'Haight-Ashbury': 6/60,
            'Russian Hill': 18/60,
            'Marina District': 21/60,
            'Richmond District': 16/60,
            'Union Square': 19/60,
            'Sunset District': 17/60,
        },
        'Marina District': {
            'Financial District': 17/60,
            'Fisherman\'s Wharf': 10/60,
            'Presidio': 10/60,
            'Bayview': 27/60,
            'Haight-Ashbury': 16/60,
            'Russian Hill': 8/60,
            'The Castro': 22/60,
            'Richmond District': 11/60,
            'Union Square': 16/60,
            'Sunset District': 19/60,
        },
        'Richmond District': {
            'Financial District': 22/60,
            'Fisherman\'s Wharf': 18/60,
            'Presidio': 7/60,
            'Bayview': 27/60,
            'Haight-Ashbury': 10/60,
            'Russian Hill': 13/60,
            'The Castro': 16/60,
            'Marina District': 9/60,
            'Union Square': 21/60,
            'Sunset District': 11/60,
        },
        'Union Square': {
            'Financial District': 9/60,
            'Fisherman\'s Wharf': 15/60,
            'Presidio': 24/60,
            'Bayview': 15/60,
            'Haight-Ashbury': 18/60,
            'Russian Hill': 13/60,
            'The Castro': 17/60,
            'Marina District': 18/60,
            'Richmond District': 20/60,
            'Sunset District': 27/60,
        },
        'Sunset District': {
            'Financial District': 30/60,
            'Fisherman\'s Wharf': 29/60,
            'Presidio': 16/60,
            'Bayview': 22/60,
            'Haight-Ashbury': 15/60,
            'Russian Hill': 24/60,
            'The Castro': 17/60,
            'Marina District': 21/60,
            'Richmond District': 12/60,
            'Union Square': 30/60,
        }
    }

    # Create variables for each friend's meeting start and end times
    start_vars = {}
    end_vars = {}
    for name in friends:
        start_vars[name] = Real(f'start_{name}')
        end_vars[name] = Real(f'end_{name}')

    # Constraints for each friend's meeting time window and duration
    for name in friends:
        friend = friends[name]
        s.add(start_vars[name] >= friend['start_window'])
        s.add(end_vars[name] <= friend['end_window'])
        s.add(end_vars[name] >= start_vars[name] + friend['min_duration'])

    # Initial location is Financial District at 9:00 AM
    current_time = 9.0
    current_location = 'Financial District'

    # To model the sequence of meetings, we need to order them.
    # This is complex, so we'll instead ensure that for any two meetings, they don't overlap and travel time is respected.
    # We'll use a list of all possible meeting pairs.
    meeting_names = list(friends.keys())
    for i in range(len(meeting_names)):
        for j in range(i+1, len(meeting_names)):
            name1 = meeting_names[i]
            name2 = meeting_names[j]
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            # Either meeting1 is before meeting2 or vice versa
            before = And(
                end_vars[name1] + travel_times[loc1][loc2] <= start_vars[name2],
            )
            after = And(
                end_vars[name2] + travel_times[loc2][loc1] <= start_vars[name1],
            )
            s.add(Or(before, after))

    # Also, the first meeting must start after current_time + travel time from current_location
    for name in friends:
        loc = friends[name]['location']
        s.add(start_vars[name] >= current_time + travel_times[current_location][loc])

    # To maximize the number of friends met, we'll use a pseudo-Boolean approach.
    # We'll create a variable for each friend indicating whether they are met.
    met = {}
    for name in friends:
        met[name] = Bool(f'met_{name}')
        # If the meeting is scheduled, met is true
        s.add(met[name] == (start_vars[name] >= friends[name]['start_window']))

    # Maximize the number of friends met
    num_met = Int('num_met')
    s.add(num_met == Sum([If(met[name], 1, 0) for name in friends]))
    s.maximize(num_met)

    if s.check() == sat:
        model = s.model()
        print("Optimal schedule to meet the maximum number of friends:")
        scheduled = []
        for name in friends:
            if is_true(model[met[name]]):
                # Convert model values to float properly
                start_val = model[start_vars[name]]
                end_val = model[end_vars[name]]
                start = float(start_val.numerator_as_long())/float(start_val.denominator_as_long())
                end = float(end_val.numerator_as_long())/float(end_val.denominator_as_long())
                scheduled.append((name, start, end))
        scheduled.sort(key=lambda x: x[1])
        for name, start, end in scheduled:
            start_hour = int(start)
            start_minute = int((start - start_hour) * 60 + 0.5)  # Round to nearest minute
            end_hour = int(end)
            end_minute = int((end - end_hour) * 60 + 0.5)  # Round to nearest minute
            print(f"Meet {name} at {friends[name]['location']} from {start_hour}:{start_minute:02d} to {end_hour}:{end_minute:02d}")
    else:
        print("No solution found to meet any friends.")

solve_scheduling()