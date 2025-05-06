from z3 import *

def main():
    friends_data = [
        {'name': 'Andrew', 'location': 'Golden Gate Park', 'start': 705, 'end': 870, 'min_duration': 75},
        {'name': 'Sarah', 'location': 'Pacific Heights', 'start': 975, 'end': 1125, 'min_duration': 15},
        {'name': 'Nancy', 'location': 'Presidio', 'start': 1050, 'end': 1155, 'min_duration': 60},
        {'name': 'Rebecca', 'location': 'Chinatown', 'start': 585, 'end': 1290, 'min_duration': 90},
        {'name': 'Robert', 'location': 'The Castro', 'start': 510, 'end': 855, 'min_duration': 30},
    ]

    travel_times = {
        'Union Square': {
            'Golden Gate Park': 22, 'Pacific Heights': 15, 'Presidio': 24,
            'Chinatown': 7, 'The Castro': 19
        },
        'Golden Gate Park': {
            'Union Square': 22, 'Pacific Heights': 16, 'Presidio': 11,
            'Chinatown': 23, 'The Castro': 13
        },
        'Pacific Heights': {
            'Union Square': 12, 'Golden Gate Park': 15, 'Presidio': 11,
            'Chinatown': 11, 'The Castro': 16
        },
        'Presidio': {
            'Union Square': 22, 'Golden Gate Park': 12, 'Pacific Heights': 11,
            'Chinatown': 21, 'The Castro': 21
        },
        'Chinatown': {
            'Union Square': 7, 'Golden Gate Park': 23, 'Pacific Heights': 10,
            'Presidio': 19, 'The Castro': 22
        },
        'The Castro': {
            'Union Square': 19, 'Golden Gate Park': 11, 'Pacific Heights': 16,
            'Presidio': 20, 'Chinatown': 20
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
        
        # From starting point (Union Square at 540 minutes = 9:00AM)
        travel_time = travel_times['Union Square'].get(friend['location'], 0)
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