from z3 import *

def main():
    friends_data = [
        {'name': 'David', 'location': 'Sunset District', 'start': 555, 'end': 1320, 'min_duration': 15},
        {'name': 'Kenneth', 'location': 'Union Square', 'start': 1290, 'end': 1305, 'min_duration': 15},
        {'name': 'Patricia', 'location': 'Nob Hill', 'start': 900, 'end': 1230, 'min_duration': 120},
        {'name': 'Mary', 'location': 'Marina District', 'start': 885, 'end': 1005, 'min_duration': 45},
        {'name': 'Charles', 'location': 'Richmond District', 'start': 1035, 'end': 1260, 'min_duration': 15},
        {'name': 'Joshua', 'location': 'Financial District', 'start': 870, 'end': 1035, 'min_duration': 90},
        {'name': 'Ronald', 'location': 'Embarcadero', 'start': 1095, 'end': 1245, 'min_duration': 30},
        {'name': 'George', 'location': 'The Castro', 'start': 855, 'end': 1260, 'min_duration': 105},
        {'name': 'Kimberly', 'location': 'Alamo Square', 'start': 540, 'end': 870, 'min_duration': 105},
        {'name': 'William', 'location': 'Presidio', 'start': 540, 'end': 765, 'min_duration': 60},
    ]

    travel_times = {
        'Russian Hill': {
            'Sunset District': 23, 'Union Square': 10, 'Nob Hill': 5,
            'Marina District': 7, 'Richmond District': 14, 'Financial District': 11,
            'Embarcadero': 8, 'The Castro': 21, 'Alamo Square': 15, 'Presidio': 14
        },
        'Sunset District': {
            'Russian Hill': 24, 'Union Square': 30, 'Nob Hill': 27,
            'Marina District': 21, 'Richmond District': 12, 'Financial District': 30,
            'Embarcadero': 30, 'The Castro': 17, 'Alamo Square': 17, 'Presidio': 16
        },
        'Union Square': {
            'Russian Hill': 13, 'Sunset District': 27, 'Nob Hill': 9,
            'Marina District': 18, 'Richmond District': 20, 'Financial District': 9,
            'Embarcadero': 11, 'The Castro': 17, 'Alamo Square': 15, 'Presidio': 24
        },
        'Nob Hill': {
            'Russian Hill': 5, 'Sunset District': 24, 'Union Square': 7,
            'Marina District': 11, 'Richmond District': 14, 'Financial District': 9,
            'Embarcadero': 9, 'The Castro': 17, 'Alamo Square': 11, 'Presidio': 17
        },
        'Marina District': {
            'Russian Hill': 8, 'Sunset District': 19, 'Union Square': 16,
            'Nob Hill': 12, 'Richmond District': 11, 'Financial District': 17,
            'Embarcadero': 14, 'The Castro': 22, 'Alamo Square': 15, 'Presidio': 10
        },
        'Richmond District': {
            'Russian Hill': 13, 'Sunset District': 11, 'Union Square': 21,
            'Nob Hill': 17, 'Marina District': 9, 'Financial District': 22,
            'Embarcadero': 19, 'The Castro': 16, 'Alamo Square': 13, 'Presidio': 7
        },
        'Financial District': {
            'Russian Hill': 11, 'Sunset District': 30, 'Union Square': 9,
            'Nob Hill': 8, 'Marina District': 15, 'Richmond District': 21,
            'Embarcadero': 4, 'The Castro': 20, 'Alamo Square': 17, 'Presidio': 22
        },
        'Embarcadero': {
            'Russian Hill': 8, 'Sunset District': 30, 'Union Square': 10,
            'Nob Hill': 10, 'Marina District': 12, 'Richmond District': 21,
            'Financial District': 5, 'The Castro': 25, 'Alamo Square': 19, 'Presidio': 20
        },
        'The Castro': {
            'Russian Hill': 18, 'Sunset District': 17, 'Union Square': 19,
            'Nob Hill': 16, 'Marina District': 21, 'Richmond District': 16,
            'Financial District': 21, 'Embarcadero': 22, 'Alamo Square': 8, 'Presidio': 20
        },
        'Alamo Square': {
            'Russian Hill': 13, 'Sunset District': 16, 'Union Square': 14,
            'Nob Hill': 11, 'Marina District': 15, 'Richmond District': 11,
            'Financial District': 17, 'Embarcadero': 16, 'The Castro': 8, 'Presidio': 17
        },
        'Presidio': {
            'Russian Hill': 14, 'Sunset District': 15, 'Union Square': 22,
            'Nob Hill': 18, 'Marina District': 11, 'Richmond District': 7,
            'Financial District': 23, 'Embarcadero': 20, 'The Castro': 21, 'Alamo Square': 19
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
        
        # From starting point (Russian Hill at 540 minutes)
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