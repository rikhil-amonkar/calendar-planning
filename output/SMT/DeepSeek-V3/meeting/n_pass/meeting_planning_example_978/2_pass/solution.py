from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friends data
    friends = {
        'Stephanie': {'location': 'Fisherman\'s Wharf', 'start': 15.5, 'end': 22.0, 'min_duration': 0.5},
        'Lisa': {'location': 'Financial District', 'start': 10.75, 'end': 17.25, 'min_duration': 0.25},
        'Melissa': {'location': 'Russian Hill', 'start': 17.0, 'end': 21.75, 'min_duration': 2.0},
        'Betty': {'location': 'Marina District', 'start': 10.75, 'end': 14.25, 'min_duration': 1.0},
        'Sarah': {'location': 'Richmond District', 'start': 16.25, 'end': 19.5, 'min_duration': 1.75},
        'Daniel': {'location': 'Pacific Heights', 'start': 18.5, 'end': 21.75, 'min_duration': 1.0},
        'Joshua': {'location': 'Haight-Ashbury', 'start': 9.0, 'end': 15.5, 'min_duration': 0.25},
        'Joseph': {'location': 'Presidio', 'start': 7.0, 'end': 13.0, 'min_duration': 0.75},
        'Andrew': {'location': 'Nob Hill', 'start': 19.75, 'end': 22.0, 'min_duration': 1.75},
        'John': {'location': 'The Castro', 'start': 13.25, 'end': 19.75, 'min_duration': 0.75}
    }

    # Travel times (minutes converted to hours)
    travel_times = {
        'Embarcadero': {'Fisherman\'s Wharf': 6/60, 'Financial District': 5/60, 'Russian Hill': 8/60,
                        'Marina District': 12/60, 'Richmond District': 21/60, 'Pacific Heights': 11/60,
                        'Haight-Ashbury': 21/60, 'Presidio': 20/60, 'Nob Hill': 10/60, 'The Castro': 25/60},
        'Fisherman\'s Wharf': {'Embarcadero': 8/60, 'Financial District': 11/60, 'Russian Hill': 7/60,
                              'Marina District': 9/60, 'Richmond District': 18/60, 'Pacific Heights': 12/60,
                              'Haight-Ashbury': 22/60, 'Presidio': 17/60, 'Nob Hill': 11/60, 'The Castro': 27/60},
        'Financial District': {'Embarcadero': 4/60, 'Fisherman\'s Wharf': 10/60, 'Russian Hill': 11/60,
                              'Marina District': 15/60, 'Richmond District': 21/60, 'Pacific Heights': 13/60,
                              'Haight-Ashbury': 19/60, 'Presidio': 22/60, 'Nob Hill': 8/60, 'The Castro': 20/60},
        'Russian Hill': {'Embarcadero': 8/60, 'Fisherman\'s Wharf': 7/60, 'Financial District': 11/60,
                        'Marina District': 7/60, 'Richmond District': 14/60, 'Pacific Heights': 7/60,
                        'Haight-Ashbury': 17/60, 'Presidio': 14/60, 'Nob Hill': 5/60, 'The Castro': 21/60},
        'Marina District': {'Embarcadero': 14/60, 'Fisherman\'s Wharf': 10/60, 'Financial District': 17/60,
                           'Russian Hill': 8/60, 'Richmond District': 11/60, 'Pacific Heights': 7/60,
                           'Haight-Ashbury': 16/60, 'Presidio': 10/60, 'Nob Hill': 12/60, 'The Castro': 22/60},
        'Richmond District': {'Embarcadero': 19/60, 'Fisherman\'s Wharf': 18/60, 'Financial District': 22/60,
                              'Russian Hill': 13/60, 'Marina District': 9/60, 'Pacific Heights': 10/60,
                              'Haight-Ashbury': 10/60, 'Presidio': 7/60, 'Nob Hill': 17/60, 'The Castro': 16/60},
        'Pacific Heights': {'Embarcadero': 10/60, 'Fisherman\'s Wharf': 13/60, 'Financial District': 13/60,
                           'Russian Hill': 7/60, 'Marina District': 6/60, 'Richmond District': 12/60,
                           'Haight-Ashbury': 11/60, 'Presidio': 11/60, 'Nob Hill': 8/60, 'The Castro': 16/60},
        'Haight-Ashbury': {'Embarcadero': 20/60, 'Fisherman\'s Wharf': 23/60, 'Financial District': 21/60,
                           'Russian Hill': 17/60, 'Marina District': 17/60, 'Richmond District': 10/60,
                           'Pacific Heights': 12/60, 'Presidio': 15/60, 'Nob Hill': 15/60, 'The Castro': 6/60},
        'Presidio': {'Embarcadero': 20/60, 'Fisherman\'s Wharf': 19/60, 'Financial District': 23/60,
                    'Russian Hill': 14/60, 'Marina District': 11/60, 'Richmond District': 7/60,
                    'Pacific Heights': 11/60, 'Haight-Ashbury': 15/60, 'Nob Hill': 18/60, 'The Castro': 21/60},
        'Nob Hill': {'Embarcadero': 9/60, 'Fisherman\'s Wharf': 10/60, 'Financial District': 9/60,
                     'Russian Hill': 5/60, 'Marina District': 11/60, 'Richmond District': 14/60,
                     'Pacific Heights': 8/60, 'Haight-Ashbury': 13/60, 'Presidio': 17/60, 'The Castro': 17/60},
        'The Castro': {'Embarcadero': 22/60, 'Fisherman\'s Wharf': 24/60, 'Financial District': 21/60,
                      'Russian Hill': 18/60, 'Marina District': 21/60, 'Richmond District': 16/60,
                      'Pacific Heights': 16/60, 'Haight-Ashbury': 6/60, 'Presidio': 20/60, 'Nob Hill': 16/60}
    }

    # Decision variables
    meet = {name: Bool(f'meet_{name}') for name in friends}
    start = {name: Real(f'start_{name}') for name in friends}
    duration = {name: Real(f'duration_{name}') for name in friends}
    order = {name: Int(f'order_{name}') for name in friends}

    # Constraints for each friend
    for name in friends:
        s.add(Implies(meet[name], start[name] >= friends[name]['start']))
        s.add(Implies(meet[name], start[name] + duration[name] <= friends[name]['end']))
        s.add(Implies(meet[name], duration[name] >= friends[name]['min_duration']))
        s.add(Implies(meet[name], order[name] >= 0))
        s.add(Implies(Not(meet[name]), order[name] == -1))

    # All meeting orders must be distinct
    s.add(Distinct([If(meet[name], order[name], -1) for name in friends]))

    # Travel time constraints between consecutive meetings
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                travel_time = travel_times[loc1][loc2]
                s.add(Implies(And(meet[name1], meet[name2], order[name1] + 1 == order[name2]),
                      start[name2] >= start[name1] + duration[name1] + travel_time))

    # Initial constraints (starting at Embarcadero at 9:00 AM)
    first_meeting = [If(And(meet[name], order[name] == 0), 
                     start[name] >= 9.0 + travel_times['Embarcadero'][friends[name]['location']],
                     True) for name in friends]
    s.add(Or([And(meet[name], order[name] == 0) for name in friends] + [And([Not(meet[name]) for name in friends])]))

    # Maximize number of friends met
    s.maximize(Sum([If(meet[name], 1, 0) for name in friends]))

    # Solve
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        scheduled = sorted([(name, m.evaluate(order[name]).as_long()) 
                          for name in friends if m.evaluate(meet[name])], 
                          key=lambda x: x[1])
        
        current_location = 'Embarcadero'
        current_time = 9.0
        
        for name, _ in scheduled:
            loc = friends[name]['location']
            travel_time = travel_times[current_location][loc]
            current_time += travel_time
            start_time = m.evaluate(start[name]).as_decimal(3)
            end_time = start_time + m.evaluate(duration[name]).as_decimal(3)
            
            print(f"Travel from {current_location} to {loc} ({travel_time*60:.0f} min)")
            print(f"Meet {name} at {loc} from {float(start_time):.2f} to {float(end_time):.2f}")
            
            current_location = loc
            current_time = float(end_time)
    else:
        print("No valid schedule found")

solve_scheduling()