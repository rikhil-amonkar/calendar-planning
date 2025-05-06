from z3 import *

def main():
    friends_data = [
        {'name': 'Brian', 'location': 'North Beach', 'start': 780, 'end': 1140, 'min_duration': 90},
        {'name': 'Richard', 'location': 'Fisherman\'s Wharf', 'start': 660, 'end': 765, 'min_duration': 60},
        {'name': 'Ashley', 'location': 'Haight-Ashbury', 'start': 900, 'end': 1230, 'min_duration': 90},
        {'name': 'Elizabeth', 'location': 'Nob Hill', 'start': 705, 'end': 1110, 'min_duration': 75},
        {'name': 'Jessica', 'location': 'Golden Gate Park', 'start': 1200, 'end': 1305, 'min_duration': 105},
        {'name': 'Deborah', 'location': 'Union Square', 'start': 1050, 'end': 1320, 'min_duration': 60},
        {'name': 'Kimberly', 'location': 'Alamo Square', 'start': 1050, 'end': 1275, 'min_duration': 45},
        {'name': 'Kenneth', 'location': 'Chinatown', 'start': 825, 'end': 1170, 'min_duration': 105},
        {'name': 'Anthony', 'location': 'Pacific Heights', 'start': 855, 'end': 960, 'min_duration': 30},
    ]

    travel_times = {
        'Bayview': {
            'North Beach': 22,
            'Fisherman\'s Wharf': 25,
            'Haight-Ashbury': 19,
            'Nob Hill': 20,
            'Golden Gate Park': 22,
            'Union Square': 18,
            'Alamo Square': 16,
            'Chinatown': 19,
            'Pacific Heights': 23,
        },
        'North Beach': {
            'Bayview': 25,
            'Fisherman\'s Wharf': 5,
            'Haight-Ashbury': 18,
            'Nob Hill': 7,
            'Golden Gate Park': 22,
            'Union Square': 7,
            'Alamo Square': 16,
            'Chinatown': 6,
            'Pacific Heights': 8,
        },
        'Fisherman\'s Wharf': {
            'Bayview': 26,
            'North Beach': 6,
            'Haight-Ashbury': 22,
            'Nob Hill': 11,
            'Golden Gate Park': 25,
            'Union Square': 13,
            'Alamo Square': 21,
            'Chinatown': 12,
            'Pacific Heights': 12,
        },
        'Haight-Ashbury': {
            'Bayview': 18,
            'North Beach': 19,
            'Fisherman\'s Wharf': 23,
            'Nob Hill': 15,
            'Golden Gate Park': 7,
            'Union Square': 19,
            'Alamo Square': 5,
            'Chinatown': 19,
            'Pacific Heights': 12,
        },
        'Nob Hill': {
            'Bayview': 19,
            'North Beach': 8,
            'Fisherman\'s Wharf': 10,
            'Haight-Ashbury': 13,
            'Golden Gate Park': 17,
            'Union Square': 7,
            'Alamo Square': 11,
            'Chinatown': 6,
            'Pacific Heights': 8,
        },
        'Golden Gate Park': {
            'Bayview': 23,
            'North Beach': 23,
            'Fisherman\'s Wharf': 24,
            'Haight-Ashbury': 7,
            'Nob Hill': 20,
            'Union Square': 22,
            'Alamo Square': 9,
            'Chinatown': 23,
            'Pacific Heights': 16,
        },
        'Union Square': {
            'Bayview': 15,
            'North Beach': 10,
            'Fisherman\'s Wharf': 15,
            'Haight-Ashbury': 18,
            'Nob Hill': 9,
            'Golden Gate Park': 22,
            'Alamo Square': 15,
            'Chinatown': 7,
            'Pacific Heights': 15,
        },
        'Alamo Square': {
            'Bayview': 16,
            'North Beach': 15,
            'Fisherman\'s Wharf': 19,
            'Haight-Ashbury': 5,
            'Nob Hill': 11,
            'Golden Gate Park': 9,
            'Union Square': 14,
            'Chinatown': 15,
            'Pacific Heights': 10,
        },
        'Chinatown': {
            'Bayview': 20,
            'North Beach': 3,
            'Fisherman\'s Wharf': 8,
            'Haight-Ashbury': 19,
            'Nob Hill': 9,
            'Golden Gate Park': 23,
            'Union Square': 7,
            'Alamo Square': 17,
            'Pacific Heights': 10,
        },
        'Pacific Heights': {
            'Bayview': 22,
            'North Beach': 9,
            'Fisherman\'s Wharf': 13,
            'Haight-Ashbury': 11,
            'Nob Hill': 8,
            'Golden Gate Park': 15,
            'Union Square': 12,
            'Alamo Square': 10,
            'Chinatown': 11,
        },
    }

    opt = Optimize()

    for friend in friends_data:
        friend['met'] = Bool(f"met_{friend['name']}")
        friend['start'] = Real(f"start_{friend['name']}")
        friend['end'] = Real(f"end_{friend['name']}")

    for friend in friends_data:
        met = friend['met']
        start = friend['start']
        end = friend['end']
        opt.add(Implies(met, start >= friend['start']))
        opt.add(Implies(met, end <= friend['end']))
        opt.add(Implies(met, end == start + friend['min_duration']))
        from_bayview = 540 + travel_times['Bayview'][friend['location']]
        predecessor_conds = [start >= from_bayview]
        for other in friends_data:
            if other['name'] == friend['name']:
                continue
            travel = travel_times[other['location']][friend['location']]
            cond = And(other['met'], start >= other['end'] + travel)
            predecessor_conds.append(cond)
        opt.add(Implies(met, Or(predecessor_conds)))

    opt.maximize(Sum([If(friend['met'], 1, 0) for friend in friends_data]))

    if opt.check() == sat:
        model = opt.model()
        total = 0
        print("Schedule:")
        for friend in friends_data:
            if model.evaluate(friend['met']):
                total += 1
                start_val = model.evaluate(friend['start']).as_long()
                end_val = model.evaluate(friend['end']).as_long()
                start_h, start_m = divmod(start_val, 60)
                end_h, end_m = divmod(end_val, 60)
                print(f"{friend['name']}: {start_h:02d}:{start_m:02d} to {end_h:02d}:{end_m:02d}")
        print(f"Total friends met: {total}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()