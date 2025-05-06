from z3 import *

def main():
    friends_data = [
        {'name': 'David', 'location': 'Chinatown', 'start': 960, 'end': 1305, 'min_duration': 105},
    ]

    travel_times = {
        'Golden Gate Park': {'Chinatown': 23},
        'Chinatown': {'Golden Gate Park': 23}
    }

    opt = Optimize()

    # Create variables for the friend
    for friend in friends_data:
        friend['met'] = Bool(f"met_{friend['name']}")
        friend['start_var'] = Real(f"start_{friend['name']}")
        friend['end_var'] = Real(f"end_{friend['name']}")

    # Add constraints for the friend
    for friend in friends_data:
        met = friend['met']
        start = friend['start_var']
        end = friend['end_var']
        
        # Time window and duration constraints
        opt.add(Implies(met, start >= friend['start']))
        opt.add(Implies(met, end <= friend['end']))
        opt.add(Implies(met, end == start + friend['min_duration']))
        
        # Travel constraints from starting point (Golden Gate Park at 540 minutes)
        travel_time = travel_times['Golden Gate Park'][friend['location']]
        from_start = 540 + travel_time
        opt.add(Implies(met, start >= from_start))

    # Maximize meeting David
    opt.maximize(If(friends_data[0]['met'], 1, 0))

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