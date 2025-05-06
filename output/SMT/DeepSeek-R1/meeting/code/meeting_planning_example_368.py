from z3 import *

def main():
    friends_data = [
        {'name': 'Joseph', 'location': 'Russian Hill', 'start': 510, 'end': 1155, 'min_duration': 60},
        {'name': 'Nancy', 'location': 'Alamo Square', 'start': 660, 'end': 960, 'min_duration': 90},
        {'name': 'Jason', 'location': 'North Beach', 'start': 1005, 'end': 1305, 'min_duration': 15},
        {'name': 'Jeffrey', 'location': 'Financial District', 'start': 630, 'end': 945, 'min_duration': 45}
    ]

    travel_times = {
        'Bayview': {
            'Russian Hill': 23, 'Alamo Square': 16, 'North Beach': 21, 'Financial District': 19
        },
        'Russian Hill': {
            'Bayview': 23, 'Alamo Square': 15, 'North Beach': 5, 'Financial District': 11
        },
        'Alamo Square': {
            'Bayview': 16, 'Russian Hill': 13, 'North Beach': 15, 'Financial District': 17
        },
        'North Beach': {
            'Bayview': 22, 'Russian Hill': 4, 'Alamo Square': 16, 'Financial District': 8
        },
        'Financial District': {
            'Bayview': 19, 'Russian Hill': 10, 'Alamo Square': 17, 'North Beach': 7
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
        
        # From starting point (Bayview at 540 minutes)
        travel_time = travel_times['Bayview'].get(friend['location'], 0)
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