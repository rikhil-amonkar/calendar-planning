from z3 import *

def main():
    friends_data = [
        {'name': 'Linda', 'location': 'Marina District', 'start': 1080, 'end': 1320, 'min_duration': 30},
        {'name': 'Kenneth', 'location': 'The Castro', 'start': 885, 'end': 975, 'min_duration': 30},
        {'name': 'Kimberly', 'location': 'Richmond District', 'start': 855, 'end': 1320, 'min_duration': 30},
        {'name': 'Paul', 'location': 'Alamo Square', 'start': 1260, 'end': 1290, 'min_duration': 15},
        {'name': 'Carol', 'location': 'Financial District', 'start': 615, 'end': 720, 'min_duration': 60},
        {'name': 'Brian', 'location': 'Presidio', 'start': 600, 'end': 1290, 'min_duration': 75},
        {'name': 'Laura', 'location': 'Mission District', 'start': 975, 'end': 1230, 'min_duration': 30},
        {'name': 'Sandra', 'location': 'Nob Hill', 'start': 555, 'end': 1110, 'min_duration': 60},
        {'name': 'Karen', 'location': 'Russian Hill', 'start': 1110, 'end': 1320, 'min_duration': 75},
    ]

    travel_times = {
        'Pacific Heights': {
            'Marina District': 6,
            'The Castro': 16,
            'Richmond District': 12,
            'Alamo Square': 10,
            'Financial District': 13,
            'Presidio': 11,
            'Mission District': 15,
            'Nob Hill': 8,
            'Russian Hill': 7,
        },
        'Marina District': {
            'Pacific Heights': 7,
            'The Castro': 22,
            'Richmond District': 11,
            'Alamo Square': 15,
            'Financial District': 17,
            'Presidio': 10,
            'Mission District': 20,
            'Nob Hill': 12,
            'Russian Hill': 8,
        },
        'The Castro': {
            'Pacific Heights': 16,
            'Marina District': 21,
            'Richmond District': 16,
            'Alamo Square': 8,
            'Financial District': 21,
            'Presidio': 20,
            'Mission District': 7,
            'Nob Hill': 16,
            'Russian Hill': 18,
        },
        'Richmond District': {
            'Pacific Heights': 10,
            'Marina District': 9,
            'The Castro': 16,
            'Alamo Square': 13,
            'Financial District': 22,
            'Presidio': 7,
            'Mission District': 20,
            'Nob Hill': 17,
            'Russian Hill': 13,
        },
        'Alamo Square': {
            'Pacific Heights': 10,
            'Marina District': 15,
            'The Castro': 8,
            'Richmond District': 11,
            'Financial District': 17,
            'Presidio': 17,
            'Mission District': 10,
            'Nob Hill': 11,
            'Russian Hill': 13,
        },
        'Financial District': {
            'Pacific Heights': 13,
            'Marina District': 15,
            'The Castro': 20,
            'Richmond District': 21,
            'Alamo Square': 17,
            'Presidio': 22,
            'Mission District': 17,
            'Nob Hill': 8,
            'Russian Hill': 11,
        },
        'Presidio': {
            'Pacific Heights': 11,
            'Marina District': 11,
            'The Castro': 21,
            'Richmond District': 7,
            'Alamo Square': 19,
            'Financial District': 23,
            'Mission District': 26,
            'Nob Hill': 18,
            'Russian Hill': 14,
        },
        'Mission District': {
            'Pacific Heights': 16,
            'Marina District': 19,
            'The Castro': 7,
            'Richmond District': 20,
            'Alamo Square': 11,
            'Financial District': 15,
            'Presidio': 25,
            'Nob Hill': 12,
            'Russian Hill': 15,
        },
        'Nob Hill': {
            'Pacific Heights': 8,
            'Marina District': 11,
            'The Castro': 17,
            'Richmond District': 14,
            'Alamo Square': 11,
            'Financial District': 9,
            'Presidio': 17,
            'Mission District': 13,
            'Russian Hill': 5,
        },
        'Russian Hill': {
            'Pacific Heights': 7,
            'Marina District': 7,
            'The Castro': 21,
            'Richmond District': 14,
            'Alamo Square': 15,
            'Financial District': 11,
            'Presidio': 14,
            'Mission District': 16,
            'Nob Hill': 5,
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

        initial_location = 'Pacific Heights'
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