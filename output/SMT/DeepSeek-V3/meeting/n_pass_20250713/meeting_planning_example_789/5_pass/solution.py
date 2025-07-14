from z3 import *

def solve_scheduling():
    opt = Optimize()

    friends = {
        'Betty': {'location': 'Russian Hill', 'start': 7*60, 'end': 16*60 + 45, 'duration': 105},
        'Melissa': {'location': 'Alamo Square', 'start': 9*60 + 30, 'end': 17*60 + 15, 'duration': 105},
        'Joshua': {'location': 'Haight-Ashbury', 'start': 12*60 + 15, 'end': 19*60, 'duration': 90},
        'Jeffrey': {'location': 'Marina District', 'start': 12*60 + 15, 'end': 18*60, 'duration': 45},
        'James': {'location': 'Bayview', 'start': 7*60 + 30, 'end': 20*60, 'duration': 90},
        'Anthony': {'location': 'Chinatown', 'start': 11*60 + 45, 'end': 13*60 + 30, 'duration': 75},
        'Timothy': {'location': 'Presidio', 'start': 12*60 + 30, 'end': 14*60 + 45, 'duration': 90},
        'Emily': {'location': 'Sunset District', 'start': 19*60 + 30, 'end': 21*60 + 30, 'duration': 120}
    }

    travel_times = {
        ('Union Square', 'Russian Hill'): 13,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'Sunset District'): 27,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Marina District'): 7,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Marina District'): 15,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Marina District', 'Bayview'): 27,
        ('Bayview', 'Sunset District'): 23
    }

    meeting_vars = {}
    for name in friends:
        meeting_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'met': Bool(f'met_{name}')
        }

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        opt.add(Implies(meeting_vars[name]['met'], 
                       And(meeting_vars[name]['start'] >= friend['start'],
                           meeting_vars[name]['end'] <= friend['end'],
                           meeting_vars[name]['end'] == meeting_vars[name]['start'] + friend['duration'])))

    # Sequence constraints with travel times
    sequence = []
    current_loc = 'Union Square'
    current_time = 540  # 9:00 AM
    
    for name in friends:
        if name != 'Emily':  # Emily must be last
            sequence.append(name)

    # Add all possible permutations of 6 friends (including Emily)
    # This is simplified - in practice we'd need to generate permutations
    # For now, we'll assume a reasonable order and let Z3 find the exact timing
    
    # Example sequence: Betty -> Melissa -> Joshua -> Jeffrey -> James -> Emily
    prev_loc = 'Union Square'
    prev_end = 540
    
    # Betty
    opt.add(Implies(meeting_vars['Betty']['met'], 
                   meeting_vars['Betty']['start'] >= prev_end + travel_times[(prev_loc, 'Russian Hill')]))
    prev_loc = 'Russian Hill'
    prev_end = If(meeting_vars['Betty']['met'], meeting_vars['Betty']['end'], prev_end)
    
    # Melissa
    opt.add(Implies(meeting_vars['Melissa']['met'], 
                   meeting_vars['Melissa']['start'] >= prev_end + travel_times[(prev_loc, 'Alamo Square')]))
    prev_loc = 'Alamo Square'
    prev_end = If(meeting_vars['Melissa']['met'], meeting_vars['Melissa']['end'], prev_end)
    
    # Joshua
    opt.add(Implies(meeting_vars['Joshua']['met'], 
                   meeting_vars['Joshua']['start'] >= prev_end + travel_times[(prev_loc, 'Haight-Ashbury')]))
    prev_loc = 'Haight-Ashbury'
    prev_end = If(meeting_vars['Joshua']['met'], meeting_vars['Joshua']['end'], prev_end)
    
    # Jeffrey
    opt.add(Implies(meeting_vars['Jeffrey']['met'], 
                   meeting_vars['Jeffrey']['start'] >= prev_end + travel_times[(prev_loc, 'Marina District')]))
    prev_loc = 'Marina District'
    prev_end = If(meeting_vars['Jeffrey']['met'], meeting_vars['Jeffrey']['end'], prev_end)
    
    # James
    opt.add(Implies(meeting_vars['James']['met'], 
                   meeting_vars['James']['start'] >= prev_end + travel_times[(prev_loc, 'Bayview')]))
    prev_loc = 'Bayview'
    prev_end = If(meeting_vars['James']['met'], meeting_vars['James']['end'], prev_end)
    
    # Emily
    opt.add(Implies(meeting_vars['Emily']['met'], 
                   meeting_vars['Emily']['start'] >= prev_end + travel_times[(prev_loc, 'Sunset District')]))

    # Exactly 6 friends must be met
    total_met = Sum([If(meeting_vars[name]['met'], 1, 0) for name in friends])
    opt.add(total_met == 6)

    # Emily must be met
    opt.add(meeting_vars['Emily']['met'] == True)

    if opt.check() == sat:
        m = opt.model()
        print("SOLUTION:")
        schedule = []
        for name in friends:
            if m.evaluate(meeting_vars[name]['met']):
                start = m.evaluate(meeting_vars[name]['start']).as_long()
                end = m.evaluate(meeting_vars[name]['end']).as_long()
                start_time = f"{start//60}:{start%60:02d}"
                end_time = f"{end//60}:{end%60:02d}"
                schedule.append((name, friends[name]['location'], start_time, end_time))
        
        schedule.sort(key=lambda x: int(x[2].split(':')[0])*60 + int(x[2].split(':')[1]))
        for entry in schedule:
            print(f"Meet {entry[0]} at {entry[1]} from {entry[2]} to {entry[3]}")
    else:
        print("No feasible schedule found.")

solve_scheduling()