from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Friends' information
    friends = {
        'Nancy': {'location': 'Chinatown', 'start': 9.5, 'end': 13.5, 'min_duration': 1.5},
        'Mary': {'location': 'Alamo Square', 'start': 7.0, 'end': 21.0, 'min_duration': 1.25},
        'Jessica': {'location': 'Bayview', 'start': 11.25, 'end': 13.75, 'min_duration': 0.75},
        'Rebecca': {'location': 'Fisherman\'s Wharf', 'start': 7.0, 'end': 8.5, 'min_duration': 0.75}
    }

    # Travel times in hours
    travel = {
        ('Financial District', 'Chinatown'): 5/60,
        ('Financial District', 'Alamo Square'): 17/60,
        ('Financial District', 'Bayview'): 19/60,
        ('Financial District', 'Fisherman\'s Wharf'): 10/60,
        ('Chinatown', 'Financial District'): 5/60,
        ('Chinatown', 'Alamo Square'): 17/60,
        ('Chinatown', 'Bayview'): 22/60,
        ('Chinatown', 'Fisherman\'s Wharf'): 8/60,
        ('Alamo Square', 'Financial District'): 17/60,
        ('Alamo Square', 'Chinatown'): 16/60,
        ('Alamo Square', 'Bayview'): 16/60,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19/60,
        ('Bayview', 'Financial District'): 19/60,
        ('Bayview', 'Chinatown'): 18/60,
        ('Bayview', 'Alamo Square'): 16/60,
        ('Bayview', 'Fisherman\'s Wharf'): 25/60,
        ('Fisherman\'s Wharf', 'Financial District'): 11/60,
        ('Fisherman\'s Wharf', 'Chinatown'): 12/60,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20/60,
        ('Fisherman\'s Wharf', 'Bayview'): 26/60
    }

    # Decision variables
    meet = {f: Bool(f'meet_{f}') for f in friends}
    start = {f: Real(f'start_{f}') for f in friends}
    end = {f: Real(f'end_{f}') for f in friends}

    # Basic constraints for each friend
    for f in friends:
        info = friends[f]
        s.add(Implies(meet[f], start[f] >= info['start']))
        s.add(Implies(meet[f], end[f] <= info['end']))
        s.add(Implies(meet[f], end[f] - start[f] >= info['min_duration']))

    # Sequence constraints - try all possible meeting orders
    friend_list = list(friends.keys())
    for i in range(len(friend_list)):
        for j in range(i+1, len(friend_list)):
            f1 = friend_list[i]
            f2 = friend_list[j]
            # If both meetings happen, account for travel time
            s.add(Implies(And(meet[f1], meet[f2]),
                         Or(
                             start[f2] >= end[f1] + travel[(friends[f1]['location'], friends[f2]['location'])],
                             start[f1] >= end[f2] + travel[(friends[f2]['location'], friends[f1]['location'])]
                         )))

    # Starting from Financial District at 9:00 AM
    # First meeting must account for travel from Financial District
    first_meeting_constraints = []
    for f in friends:
        travel_time = travel[('Financial District', friends[f]['location'])]
        first_meeting_constraints.append(
            Implies(meet[f], start[f] >= 9.0 + travel_time)
        )
    s.add(Or([meet[f] for f in friends]))  # Must meet at least one friend
    s.add(And(first_meeting_constraints))

    # Objective: maximize number of friends met
    s.maximize(Sum([If(meet[f], 1, 0) for f in friends]))

    # Solve
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule found:")
        
        # Collect scheduled meetings
        scheduled = []
        for f in friends:
            if is_true(m.eval(meet[f])):
                scheduled.append((f, float(m.eval(start[f]).as_decimal(3)), 
                                float(m.eval(end[f]).as_decimal(3))))
        
        # Sort by start time
        scheduled.sort(key=lambda x: x[1])
        
        # Print schedule
        current_location = 'Financial District'
        current_time = 9.0
        total_met = 0
        
        for f, start_time, end_time in scheduled:
            travel_time = travel[(current_location, friends[f]['location'])]
            print(f"{current_time:.2f}: Travel from {current_location} to {friends[f]['location']} ({travel_time*60:.0f} min)")
            print(f"{start_time:.2f}-{end_time:.2f}: Meet {f} at {friends[f]['location']}")
            current_location = friends[f]['location']
            current_time = end_time
            total_met += 1
        
        print(f"\nTotal friends met: {total_met}")
    else:
        print("No feasible schedule found that meets all constraints.")

solve_scheduling()