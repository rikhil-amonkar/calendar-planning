from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define locations and travel times
    travel_times = {
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Bayview'): 26,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Fisherman\'s Wharf'): 22,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Bayview'): 15,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Mission District'): 13,
    }

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540

    # Friends' availability
    friends = {
        'Sarah': {
            'location': 'Fisherman\'s Wharf',
            'start': time_to_minutes(14, 45),  # 2:45 PM
            'end': time_to_minutes(17, 30),    # 5:30 PM
            'duration': 105
        },
        'Mary': {
            'location': 'Richmond District',
            'start': time_to_minutes(13, 0),   # 1:00 PM
            'end': time_to_minutes(19, 15),    # 7:15 PM
            'duration': 75
        },
        'Helen': {
            'location': 'Mission District',
            'start': time_to_minutes(21, 45),  # 9:45 PM
            'end': time_to_minutes(22, 30),    # 10:30 PM
            'duration': 30
        },
        'Thomas': {
            'location': 'Bayview',
            'start': time_to_minutes(15, 15),  # 3:15 PM
            'end': time_to_minutes(18, 45),    # 6:45 PM
            'duration': 120
        }
    }

    # Meeting variables
    meet_vars = {}
    for name in friends:
        meet_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'met': Bool(f'met_{name}')
        }

    # Initialize current state
    current_location = 'Haight-Ashbury'
    current_time = 0

    # Process each friend
    for name in friends:
        friend = friends[name]
        var = meet_vars[name]
        
        # Basic meeting constraints
        s.add(var['start'] >= friend['start'])
        s.add(var['end'] <= friend['end'])
        s.add(var['end'] == var['start'] + friend['duration'])
        
        # Travel time calculation
        travel_time = Int(f'travel_{name}')
        
        # Create condition for each possible current location
        conditions = []
        for loc in ['Haight-Ashbury', 'Fisherman\'s Wharf', 'Richmond District', 'Mission District', 'Bayview']:
            conditions.append(And(var['met'], current_location == loc, 
                               travel_time == travel_times[(loc, friend['location'])]))
        
        # Default case (not meeting)
        conditions.append(And(Not(var['met']), travel_time == 0))
        
        # Add the disjunction of all conditions
        s.add(Or(*conditions))
        
        # Update current state if meeting occurs
        current_location = If(var['met'], friend['location'], current_location)
        current_time = If(var['met'], var['end'], current_time)

    # Maximize number of friends met
    num_met = Sum([If(var['met'], 1, 0) for name, var in meet_vars.items()])
    s.maximize(num_met)

    # Solve and print results
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        for name in friends:
            if m.evaluate(meet_vars[name]['met']):
                start = m.evaluate(meet_vars[name]['start']).as_long()
                end = m.evaluate(meet_vars[name]['end']).as_long()
                h_start = (start + 540) // 60
                m_start = (start + 540) % 60
                h_end = (end + 540) // 60
                m_end = (end + 540) % 60
                print(f"Meet {name} at {friends[name]['location']} from {h_start:02d}:{m_start:02d} to {h_end:02d}:{m_end:02d}")
        print(f"Total friends met: {m.evaluate(num_met)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()