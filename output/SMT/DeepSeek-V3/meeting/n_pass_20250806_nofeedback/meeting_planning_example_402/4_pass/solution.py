from z3 import *
import json

def solve_scheduling_problem():
    opt = Optimize()

    # Travel times between locations (in minutes)
    travel_times = {
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Marina District'): 16,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Financial District'): 21,
        ('Haight-Ashbury', 'Union Square'): 17,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Financial District'): 30,
        ('Sunset District', 'Union Square'): 30,
        ('Marina District', 'Golden Gate Park'): 18,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Financial District'): 17,
        ('Marina District', 'Union Square'): 16,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Financial District', 'Haight-Ashbury'): 19,
        ('Financial District', 'Sunset District'): 31,
        ('Financial District', 'Marina District'): 15,
        ('Financial District', 'Union Square'): 9,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Haight-Ashbury'): 18,
        ('Union Square', 'Sunset District'): 26,
        ('Union Square', 'Marina District'): 18,
        ('Union Square', 'Financial District'): 9,
    }

    # Friends' availability
    friends = {
        'Sarah': {'location': 'Haight-Ashbury', 'start': 17*60, 'end': 21*60 + 30, 'duration': 105},
        'Patricia': {'location': 'Sunset District', 'start': 17*60, 'end': 19*60 + 45, 'duration': 45},
        'Matthew': {'location': 'Marina District', 'start': 9*60 + 15, 'end': 12*60, 'duration': 15},
        'Joseph': {'location': 'Financial District', 'start': 14*60 + 15, 'end': 18*60 + 45, 'duration': 30},
        'Robert': {'location': 'Union Square', 'start': 10*60 + 15, 'end': 21*60 + 45, 'duration': 15},
    }

    # Decision variables
    meet_vars = {}
    for name in friends:
        meet_vars[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'met': Bool(f'met_{name}'),
        }

    # Create variables to track location after each meeting
    location_vars = {}
    time_vars = {}
    prev_location = 'Golden Gate Park'
    prev_time = 9 * 60  # 9:00 AM
    
    # We'll process friends in a fixed order to avoid the If-in-dictionary-key issue
    friend_order = ['Matthew', 'Robert', 'Joseph', 'Patricia', 'Sarah']
    
    for i, name in enumerate(friend_order):
        friend = friends[name]
        loc = friend['location']
        
        # Travel time from previous location to current friend's location
        travel_time = travel_times[(prev_location, loc)]
        
        # If we meet this friend:
        # 1. Meeting must be within their availability window
        opt.add(Implies(meet_vars[name]['met'], 
                       And(meet_vars[name]['start'] >= friend['start'],
                           meet_vars[name]['end'] <= friend['end'],
                           meet_vars[name]['end'] == meet_vars[name]['start'] + friend['duration'])))
        
        # 2. Must have time to travel there from previous location
        opt.add(Implies(meet_vars[name]['met'],
                       meet_vars[name]['start'] >= prev_time + travel_time))
        
        # Update previous time and location
        prev_time = If(meet_vars[name]['met'], meet_vars[name]['end'], prev_time)
        prev_location = If(meet_vars[name]['met'], loc, prev_location)

    # Maximize number of friends met
    opt.maximize(Sum([If(meet_vars[name]['met'], 1, 0) for name in friends]))

    if opt.check() == sat:
        model = opt.model()
        result = []
        for name in friend_order:
            if is_true(model.eval(meet_vars[name]['met'])):
                start = model.eval(meet_vars[name]['start']).as_long()
                end = model.eval(meet_vars[name]['end']).as_long()
                result.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start//60:02d}:{start%60:02d}",
                    "end_time": f"{end//60:02d}:{end%60:02d}",
                })
        return {"itinerary": result}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))