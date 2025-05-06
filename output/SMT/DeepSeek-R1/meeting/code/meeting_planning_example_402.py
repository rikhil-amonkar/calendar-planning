from z3 import *

def main():
    friends_data = [
        {'name': 'Sarah', 'location': 'Haight-Ashbury', 'start': 1020, 'end': 1290, 'min_duration': 105},
        {'name': 'Patricia', 'location': 'Sunset District', 'start': 1020, 'end': 1185, 'min_duration': 45},
        {'name': 'Matthew', 'location': 'Marina District', 'start': 555, 'end': 720, 'min_duration': 15},
        {'name': 'Joseph', 'location': 'Financial District', 'start': 855, 'end': 1125, 'min_duration': 30},
        {'name': 'Robert', 'location': 'Union Square', 'start': 615, 'end': 1305, 'min_duration': 15},
    ]

    travel_times = {
        'Golden Gate Park': {
            'Haight-Ashbury': 7, 'Sunset District': 10, 'Marina District': 16,
            'Financial District': 26, 'Union Square': 22
        },
        'Haight-Ashbury': {
            'Golden Gate Park': 7, 'Sunset District': 15, 'Marina District': 17,
            'Financial District': 21, 'Union Square': 17
        },
        'Sunset District': {
            'Golden Gate Park': 11, 'Haight-Ashbury': 15, 'Marina District': 21,
            'Financial District': 30, 'Union Square': 30
        },
        'Marina District': {
            'Golden Gate Park': 18, 'Haight-Ashbury': 16, 'Sunset District': 19,
            'Financial District': 17, 'Union Square': 16
        },
        'Financial District': {
            'Golden Gate Park': 23, 'Haight-Ashbury': 19, 'Sunset District': 31,
            'Marina District': 15, 'Union Square': 9
        },
        'Union Square': {
            'Golden Gate Park': 22, 'Haight-Ashbury': 18, 'Sunset District': 26,
            'Marina District': 18, 'Financial District': 9
        }
    }

    opt = Optimize()

    # Create variables for each friend
    for friend in friends_data:
        friend['met'] = Bool(f"met_{friend['name']}")
        friend['start_var'] = Real(f"start_{friend['name']}")
        friend['end_var'] = Real(f"end_{friend['name']}")

    # Add constraints for each friend
    for friend in friends_data:
        met = friend['met']
        start = friend['start_var']
        end = friend['end_var']
        
        # Time window and duration constraints
        opt.add(Implies(met, start >= friend['start']))
        opt.add(Implies(met, end <= friend['end']))
        opt.add(Implies(met, end == start + friend['min_duration']))
        
        # Travel constraints from possible predecessors
        predecessor_conds = []
        
        # From starting point (Golden Gate Park at 540 minutes)
        travel_time = travel_times['Golden Gate Park'].get(friend['location'], 0)
        from_start = 540 + travel_time
        predecessor_conds.append(start >= from_start)
        
        # From other friends' locations
        for other in friends_data:
            if other['name'] == friend['name']:
                continue
            travel = travel_times[other['location']].get(friend['location'], 0)
            cond = And(other['met'], start >= other['end_var'] + travel)
            predecessor_conds.append(cond)
        
        opt.add(Implies(met, Or(*predecessor_conds)))

    # Maximize number of friends met
    opt.maximize(Sum([If(f['met'], 1, 0) for f in friends_data]))

    if opt.check() == sat:
        model = opt.model()
        schedule = []
        for friend in friends_data:
            if model.evaluate(friend['met']):
                start_val = model.evaluate(friend['start_var']).as_long()
                schedule.append((start_val, friend))
        schedule.sort()
        
        print("Optimal Schedule:")
        for time, friend in schedule:
            start_hr, start_min = divmod(time, 60)
            end_time = time + friend['min_duration']
            end_hr, end_min = divmod(end_time, 60)
            print(f"{friend['name']}: {int(start_hr):02d}:{int(start_min):02d} to {int(end_hr):02d}:{int(end_min):02d} at {friend['location']}")
        print(f"Total friends met: {len(schedule)}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()