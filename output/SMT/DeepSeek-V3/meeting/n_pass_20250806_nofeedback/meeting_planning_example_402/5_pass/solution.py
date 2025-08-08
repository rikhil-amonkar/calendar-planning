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

    # Create variables to track location and time
    # We'll model this as a sequence of decisions
    # First meeting options
    first_meeting_options = []
    for name in friends:
        friend = friends[name]
        loc = friend['location']
        travel_time = travel_times[('Golden Gate Park', loc)]
        
        # Create constraints for first meeting
        first_meeting = And(
            meet_vars[name]['met'],
            meet_vars[name]['start'] >= 9*60 + travel_time,
            meet_vars[name]['start'] >= friend['start'],
            meet_vars[name]['end'] <= friend['end'],
            meet_vars[name]['end'] == meet_vars[name]['start'] + friend['duration']
        )
        first_meeting_options.append(first_meeting)
    
    # At most one first meeting
    opt.add(AtMost(*[var['met'] for var in meet_vars.values()], 1))
    opt.add(Or(*first_meeting_options))

    # Second meeting options (if any)
    second_meeting_options = []
    for name1 in friends:
        for name2 in friends:
            if name1 == name2:
                continue
                
            friend1 = friends[name1]
            friend2 = friends[name2]
            loc1 = friend1['location']
            loc2 = friend2['location']
            
            if (loc1, loc2) not in travel_times:
                continue
                
            travel_time = travel_times[(loc1, loc2)]
            
            second_meeting = And(
                meet_vars[name1]['met'],
                meet_vars[name2]['met'],
                meet_vars[name2]['start'] >= meet_vars[name1]['end'] + travel_time,
                meet_vars[name2]['start'] >= friend2['start'],
                meet_vars[name2]['end'] <= friend2['end'],
                meet_vars[name2]['end'] == meet_vars[name2]['start'] + friend2['duration']
            )
            second_meeting_options.append(second_meeting)
    
    # Third meeting options (if any)
    third_meeting_options = []
    for name1 in friends:
        for name2 in friends:
            for name3 in friends:
                if len({name1, name2, name3}) < 3:
                    continue
                    
                friend1 = friends[name1]
                friend2 = friends[name2]
                friend3 = friends[name3]
                loc1 = friend1['location']
                loc2 = friend2['location']
                loc3 = friend3['location']
                
                if (loc1, loc2) not in travel_times or (loc2, loc3) not in travel_times:
                    continue
                    
                travel_time1 = travel_times[(loc1, loc2)]
                travel_time2 = travel_times[(loc2, loc3)]
                
                third_meeting = And(
                    meet_vars[name1]['met'],
                    meet_vars[name2]['met'],
                    meet_vars[name3]['met'],
                    meet_vars[name2]['start'] >= meet_vars[name1]['end'] + travel_time1,
                    meet_vars[name3]['start'] >= meet_vars[name2]['end'] + travel_time2,
                    meet_vars[name3]['start'] >= friend3['start'],
                    meet_vars[name3]['end'] <= friend3['end'],
                    meet_vars[name3]['end'] == meet_vars[name3]['start'] + friend3['duration']
                )
                third_meeting_options.append(third_meeting)

    # Maximize number of friends met
    opt.maximize(Sum([If(meet_vars[name]['met'], 1, 0) for name in friends]))

    if opt.check() == sat:
        model = opt.model()
        result = []
        for name in friends:
            if is_true(model.eval(meet_vars[name]['met'])):
                start = model.eval(meet_vars[name]['start']).as_long()
                end = model.eval(meet_vars[name]['end']).as_long()
                result.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start//60:02d}:{start%60:02d}",
                    "end_time": f"{end//60:02d}:{end%60:02d}",
                })
        # Sort by start time
        result.sort(key=lambda x: x['start_time'])
        return {"itinerary": result}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))