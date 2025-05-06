from z3 import *

def main():
    friends_data = [
        {'name': 'Mark', 'location': 'Marina District', 'start': 1125, 'end': 1260, 'min_duration': 90},
        {'name': 'Karen', 'location': 'Financial District', 'start': 570, 'end': 765, 'min_duration': 90},
        {'name': 'Barbara', 'location': 'Alamo Square', 'start': 600, 'end': 1170, 'min_duration': 90},
        {'name': 'Nancy', 'location': 'Golden Gate Park', 'start': 1005, 'end': 1200, 'min_duration': 105},
        {'name': 'David', 'location': 'The Castro', 'start': 540, 'end': 1080, 'min_duration': 120},
        {'name': 'Linda', 'location': 'Bayview', 'start': 1095, 'end': 1185, 'min_duration': 45},
        {'name': 'Kevin', 'location': 'Sunset District', 'start': 600, 'end': 1065, 'min_duration': 120},
        {'name': 'Matthew', 'location': 'Haight-Ashbury', 'start': 615, 'end': 930, 'min_duration': 45},
        {'name': 'Andrew', 'location': 'Nob Hill', 'start': 705, 'end': 1005, 'min_duration': 105},
    ]

    travel_times = {
        'Russian Hill': {
            'Marina District': 7, 'Financial District': 11, 'Alamo Square': 15,
            'Golden Gate Park': 21, 'The Castro': 21, 'Bayview': 23,
            'Sunset District': 23, 'Haight-Ashbury': 17, 'Nob Hill': 5
        },
        'Marina District': {
            'Russian Hill': 8, 'Financial District': 17, 'Alamo Square': 15,
            'Golden Gate Park': 18, 'The Castro': 22, 'Bayview': 27,
            'Sunset District': 19, 'Haight-Ashbury': 16, 'Nob Hill': 12
        },
        'Financial District': {
            'Russian Hill': 11, 'Marina District': 15, 'Alamo Square': 17,
            'Golden Gate Park': 23, 'The Castro': 20, 'Bayview': 19,
            'Sunset District': 30, 'Haight-Ashbury': 19, 'Nob Hill': 8
        },
        'Alamo Square': {
            'Russian Hill': 13, 'Marina District': 15, 'Financial District': 17,
            'Golden Gate Park': 9, 'The Castro': 8, 'Bayview': 16,
            'Sunset District': 16, 'Haight-Ashbury': 5, 'Nob Hill': 11
        },
        'Golden Gate Park': {
            'Russian Hill': 19, 'Marina District': 16, 'Financial District': 26,
            'Alamo Square': 9, 'The Castro': 13, 'Bayview': 23,
            'Sunset District': 10, 'Haight-Ashbury': 7, 'Nob Hill': 20
        },
        'The Castro': {
            'Russian Hill': 18, 'Marina District': 21, 'Financial District': 21,
            'Alamo Square': 8, 'Golden Gate Park': 11, 'Bayview': 19,
            'Sunset District': 17, 'Haight-Ashbury': 6, 'Nob Hill': 16
        },
        'Bayview': {
            'Russian Hill': 23, 'Marina District': 27, 'Financial District': 19,
            'Alamo Square': 16, 'Golden Gate Park': 22, 'The Castro': 19,
            'Sunset District': 23, 'Haight-Ashbury': 19, 'Nob Hill': 20
        },
        'Sunset District': {
            'Russian Hill': 24, 'Marina District': 21, 'Financial District': 30,
            'Alamo Square': 17, 'Golden Gate Park': 11, 'The Castro': 17,
            'Bayview': 22, 'Haight-Ashbury': 15, 'Nob Hill': 27
        },
        'Haight-Ashbury': {
            'Russian Hill': 17, 'Marina District': 17, 'Financial District': 21,
            'Alamo Square': 5, 'Golden Gate Park': 7, 'The Castro': 6,
            'Bayview': 18, 'Sunset District': 15, 'Nob Hill': 15
        },
        'Nob Hill': {
            'Russian Hill': 5, 'Marina District': 11, 'Financial District': 9,
            'Alamo Square': 11, 'Golden Gate Park': 17, 'The Castro': 17,
            'Bayview': 19, 'Sunset District': 24, 'Haight-Ashbury': 13
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
        
        # From starting point (Russian Hill at 540 minutes = 9:00AM)
        travel_time = travel_times['Russian Hill'].get(friend['location'], 0)
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