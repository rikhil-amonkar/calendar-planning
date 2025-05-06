from z3 import *

def main():
    friends_data = [
        {'name': 'Robert', 'location': 'Chinatown', 'start': 465, 'end': 1050, 'min_duration': 120},
        {'name': 'David', 'location': 'Sunset District', 'start': 750, 'end': 1185, 'min_duration': 45},
        {'name': 'Matthew', 'location': 'Alamo Square', 'start': 525, 'end': 825, 'min_duration': 90},
        {'name': 'Jessica', 'location': 'Financial District', 'start': 570, 'end': 1125, 'min_duration': 45},
        {'name': 'Melissa', 'location': 'North Beach', 'start': 435, 'end': 1005, 'min_duration': 45},
        {'name': 'Mark', 'location': 'Embarcadero', 'start': 915, 'end': 1080, 'min_duration': 45},
        {'name': 'Deborah', 'location': 'Presidio', 'start': 1140, 'end': 1185, 'min_duration': 45},
        {'name': 'Karen', 'location': 'Golden Gate Park', 'start': 1170, 'end': 1320, 'min_duration': 120},
        {'name': 'Laura', 'location': 'Bayview', 'start': 1290, 'end': 1335, 'min_duration': 15},
    ]

    travel_times = {
        'Richmond District': {
            'Chinatown': 20,
            'Sunset District': 11,
            'Alamo Square': 13,
            'Financial District': 22,
            'North Beach': 17,
            'Embarcadero': 19,
            'Presidio': 7,
            'Golden Gate Park': 9,
            'Bayview': 27,
        },
        'Chinatown': {
            'Richmond District': 20,
            'Sunset District': 29,
            'Alamo Square': 17,
            'Financial District': 5,
            'North Beach': 3,
            'Embarcadero': 5,
            'Presidio': 19,
            'Golden Gate Park': 23,
            'Bayview': 20,
        },
        'Sunset District': {
            'Richmond District': 12,
            'Chinatown': 30,
            'Alamo Square': 17,
            'Financial District': 30,
            'North Beach': 28,
            'Embarcadero': 30,
            'Presidio': 16,
            'Golden Gate Park': 11,
            'Bayview': 22,
        },
        'Alamo Square': {
            'Richmond District': 11,
            'Chinatown': 15,
            'Sunset District': 16,
            'Financial District': 17,
            'North Beach': 15,
            'Embarcadero': 16,
            'Presidio': 17,
            'Golden Gate Park': 9,
            'Bayview': 16,
        },
        'Financial District': {
            'Richmond District': 21,
            'Chinatown': 5,
            'Sunset District': 30,
            'Alamo Square': 17,
            'North Beach': 7,
            'Embarcadero': 4,
            'Presidio': 22,
            'Golden Gate Park': 23,
            'Bayview': 19,
        },
        'North Beach': {
            'Richmond District': 18,
            'Chinatown': 6,
            'Sunset District': 27,
            'Alamo Square': 16,
            'Financial District': 8,
            'Embarcadero': 6,
            'Presidio': 17,
            'Golden Gate Park': 22,
            'Bayview': 25,
        },
        'Embarcadero': {
            'Richmond District': 21,
            'Chinatown': 7,
            'Sunset District': 30,
            'Alamo Square': 19,
            'Financial District': 5,
            'North Beach': 5,
            'Presidio': 20,
            'Golden Gate Park': 25,
            'Bayview': 21,
        },
        'Presidio': {
            'Richmond District': 7,
            'Chinatown': 21,
            'Sunset District': 15,
            'Alamo Square': 19,
            'Financial District': 23,
            'North Beach': 18,
            'Embarcadero': 20,
            'Golden Gate Park': 12,
            'Bayview': 31,
        },
        'Golden Gate Park': {
            'Richmond District': 7,
            'Chinatown': 23,
            'Sunset District': 10,
            'Alamo Square': 9,
            'Financial District': 26,
            'North Beach': 23,
            'Embarcadero': 25,
            'Presidio': 11,
            'Bayview': 23,
        },
        'Bayview': {
            'Richmond District': 25,
            'Chinatown': 19,
            'Sunset District': 23,
            'Alamo Square': 16,
            'Financial District': 19,
            'North Beach': 22,
            'Embarcadero': 19,
            'Presidio': 32,
            'Golden Gate Park': 22,
        },
    }

    opt = Optimize()

    for friend in friends_data:
        friend['met'] = Bool(f"met_{friend['name']}")
        friend['start_var'] = Real(f"start_{friend['name']}")
        friend['end_var'] = Real(f"end_{friend['name']}")

    for friend in friends_data:
        met = friend['met']
        start = friend['start_var']
        end = friend['end_var']
        opt.add(Implies(met, start >= friend['start']))
        opt.add(Implies(met, end <= friend['end']))
        opt.add(Implies(met, end == start + friend['min_duration']))

        initial_location = 'Richmond District'
        travel_time = travel_times[initial_location][friend['location']]
        from_start = 540 + travel_time
        predecessor_conds = [start >= from_start]

        for other in friends_data:
            if other['name'] == friend['name']:
                continue
            travel = travel_times[other['location']][friend['location']]
            cond = And(other['met'], start >= other['end_var'] + travel)
            predecessor_conds.append(cond)

        opt.add(Implies(met, Or(predecessor_conds)))

    opt.maximize(Sum([If(friend['met'], 1, 0) for friend in friends_data]))

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
            print(f"{friend['name']}: {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d} at {friend['location']}")
        print(f"Total friends met: {len(schedule)}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()