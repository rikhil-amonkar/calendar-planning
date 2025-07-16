from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friend data (name: {location, start, end, min_duration})
    friends = {
        'Kevin': {'location': 'Mission District', 'start': 20.75, 'end': 21.75, 'duration': 1.0},
        'Mark': {'location': 'Fisherman\'s Wharf', 'start': 17.25, 'end': 20.0, 'duration': 1.5},
        'Jessica': {'location': 'Russian Hill', 'start': 9.0, 'end': 15.0, 'duration': 2.0},
        'Jason': {'location': 'Marina District', 'start': 15.25, 'end': 21.75, 'duration': 2.0},
        'John': {'location': 'North Beach', 'start': 9.75, 'end': 18.0, 'duration': 0.25},
        'Karen': {'location': 'Chinatown', 'start': 16.75, 'end': 19.0, 'duration': 1.25},
        'Sarah': {'location': 'Pacific Heights', 'start': 17.5, 'end': 18.25, 'duration': 0.75},
        'Amanda': {'location': 'The Castro', 'start': 20.0, 'end': 21.25, 'duration': 1.0},
        'Nancy': {'location': 'Nob Hill', 'start': 9.75, 'end': 13.0, 'duration': 0.75},
        'Rebecca': {'location': 'Sunset District', 'start': 8.75, 'end': 15.0, 'duration': 1.25}
    }

    # Travel times in hours (converted from minutes)
    travel_times = {
        ('Union Square', 'Mission District'): 14/60,
        ('Union Square', 'Fisherman\'s Wharf'): 15/60,
        ('Union Square', 'Russian Hill'): 13/60,
        ('Union Square', 'Marina District'): 18/60,
        ('Union Square', 'North Beach'): 10/60,
        ('Union Square', 'Chinatown'): 7/60,
        ('Union Square', 'Pacific Heights'): 15/60,
        ('Union Square', 'The Castro'): 17/60,
        ('Union Square', 'Nob Hill'): 9/60,
        ('Union Square', 'Sunset District'): 27/60,
        # Add all other travel times as needed
    }

    # Create variables
    meet = {name: Bool(f'meet_{name}') for name in friends}
    start_time = {name: Real(f'start_{name}') for name in friends}
    end_time = {name: Real(f'end_{name}') for name in friends}
    travel_to = {name: Real(f'travel_to_{name}') for name in friends}

    # Starting point
    current_location = 'Union Square'
    current_time = 9.0  # 9:00 AM

    # Basic constraints for each friend
    for name in friends:
        friend = friends[name]
        loc = friend['location']
        
        # If we meet this friend:
        s.add(Implies(meet[name], start_time[name] >= friend['start']))
        s.add(Implies(meet[name], end_time[name] <= friend['end']))
        s.add(Implies(meet[name], end_time[name] == start_time[name] + friend['duration']))
        
        # Travel time to this friend's location
        if (current_location, loc) in travel_times:
            s.add(Implies(meet[name], travel_to[name] == travel_times[(current_location, loc)]))
        else:
            # Default travel time if not specified
            s.add(Implies(meet[name], travel_to[name] == 0.5))  # 30 minutes default

    # Sequencing constraints (simplified - assumes we go directly to each friend)
    # In a more complete solution, we would need to model the path between friends
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                s.add(Implies(And(meet[name1], meet[name2]),
                      Or(start_time[name2] >= end_time[name1] + travel_to[name2],
                         start_time[name1] >= end_time[name2] + travel_to[name1])))

    # Maximize number of friends met
    s.maximize(Sum([If(meet[name], 1, 0) for name in friends]))

    # Solve
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print("Optimal schedule meeting these friends:")
        
        # Collect meetings and sort by start time
        meetings = []
        for name in friends:
            if is_true(m.evaluate(meet[name])):
                start = m.evaluate(start_time[name])
                end = m.evaluate(end_time[name])
                meetings.append((float(start.numerator_as_long())/float(start.denominator_as_long()),
                               name,
                               friends[name]['location']))
        
        # Sort by start time and print
        meetings.sort()
        for time, name, loc in meetings:
            print(f"{name}: at {loc} from {time:.2f} to {time + friends[name]['duration']:.2f}")
        
        print(f"\nTotal friends met: {len(meetings)}")
    else:
        print("No valid schedule found")

solve_scheduling()