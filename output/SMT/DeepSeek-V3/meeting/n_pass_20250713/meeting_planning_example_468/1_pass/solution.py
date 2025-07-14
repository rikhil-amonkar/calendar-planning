from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()
    
    # Friends and their locations
    friends = {
        'Rebecca': 'Bayview',
        'Amanda': 'Pacific Heights',
        'James': 'Alamo Square',
        'Sarah': 'Fisherman\'s Wharf',
        'Melissa': 'Golden Gate Park'
    }
    
    # Time windows (in minutes from 9:00 AM = 0)
    time_windows = {
        'Rebecca': (0, 225),  # 9:00 AM to 12:45 PM (3h45m = 225m)
        'Amanda': (570, 645),  # 6:30 PM to 9:45 PM (3h15m = 195m, but starts at 570m)
        'James': (45, 735),    # 9:45 AM to 9:15 PM (11h30m = 690m, starts at 45m)
        'Sarah': (-60, 750),   # 8:00 AM to 9:30 PM (13h30m = 810m, starts at -60m)
        'Melissa': (0, 585)    # 9:00 AM to 6:45 PM (9h45m = 585m)
    }
    
    # Minimum meeting durations (in minutes)
    min_durations = {
        'Rebecca': 90,
        'Amanda': 90,
        'James': 90,
        'Sarah': 90,
        'Melissa': 90
    }
    
    # Travel times (in minutes)
    travel_times = {
        ('The Castro', 'Bayview'): 19,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Bayview', 'The Castro'): 20,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Golden Gate Park'): 22,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Fisherman\'s Wharf', 'The Castro'): 26,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
        ('Fisherman\'s Wharf', 'Alamo Square'): 20,
        ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
        ('Golden Gate Park', 'The Castro'): 13,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24
    }
    
    # Variables for each friend: start time, end time, and whether they are met
    start_vars = {f: Int(f'start_{f}') for f in friends}
    end_vars = {f: Int(f'end_{f}') for f in friends}
    met_vars = {f: Bool(f'met_{f}') for f in friends}
    
    # Initial constraints: meeting times must be within time windows and durations
    for f in friends:
        s.add(Implies(met_vars[f], start_vars[f] >= time_windows[f][0]))
        s.add(Implies(met_vars[f], end_vars[f] <= time_windows[f][1]))
        s.add(Implies(met_vars[f], end_vars[f] == start_vars[f] + min_durations[f]))
        s.add(Implies(Not(met_vars[f]), start_vars[f] == -1))
        s.add(Implies(Not(met_vars[f]), end_vars[f] == -1))
    
    # Constraints to ensure no overlapping meetings considering travel times
    # We need to sequence the meetings properly
    # Create a list of all possible meeting orders and enforce travel times
    # This is complex, so we'll use a simplified approach by assuming a certain order
    # Alternatively, we can use a more general approach by pairwise constraints
    
    # Collect all friends that could be met
    all_friends = [f for f in friends]
    
    # For each pair of distinct friends, if both are met, enforce travel time
    for i in range(len(all_friends)):
        for j in range(len(all_friends)):
            if i == j:
                continue
            f1 = all_friends[i]
            f2 = all_friends[j]
            loc1 = friends[f1]
            loc2 = friends[f2]
            travel = travel_times.get((loc1, loc2), 0)
            s.add(Implies(And(met_vars[f1], met_vars[f2]), 
                          Or(end_vars[f1] + travel <= start_vars[f2], 
                             end_vars[f2] + travel <= start_vars[f1])))
    
    # Maximize the number of friends met
    num_met = Sum([If(met_vars[f], 1, 0) for f in friends])
    s.maximize(num_met)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Collect the meetings
        scheduled = []
        for f in friends:
            if m.evaluate(met_vars[f]):
                start = m.evaluate(start_vars[f]).as_long()
                end = m.evaluate(end_vars[f]).as_long()
                scheduled.append((f, start, end))
        # Sort by start time
        scheduled.sort(key=lambda x: x[1])
        # Print the schedule
        print("Optimal Schedule:")
        for meet in scheduled:
            f, start, end = meet
            # Convert minutes to time string
            start_time = (9 * 60 + start) % (24 * 60)
            end_time = (9 * 60 + end) % (24 * 60)
            start_h, start_m = divmod(start_time, 60)
            end_h, end_m = divmod(end_time, 60)
            print(f"Meet {f} at {friends[f]} from {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}")
        print(f"Total friends met: {len(scheduled)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()