from z3 import *

def main():
    opt = Optimize()

    friends = [
        {'name': 'Richard', 'location': 'Embarcadero', 'start': 915, 'end': 1185, 'min_duration': 90},
        {'name': 'Mark', 'location': 'Pacific Heights', 'start': 900, 'end': 1020, 'min_duration': 45},
        {'name': 'Matthew', 'location': 'Russian Hill', 'start': 1050, 'end': 1320, 'min_duration': 90},
        {'name': 'Rebecca', 'location': 'Haight-Ashbury', 'start': 885, 'end': 1080, 'min_duration': 60},
        {'name': 'Melissa', 'location': 'Golden Gate Park', 'start': 825, 'end': 1050, 'min_duration': 90},
        {'name': 'Margaret', 'location': 'Fisherman\'s Wharf', 'start': 885, 'end': 1230, 'min_duration': 15},
        {'name': 'Emily', 'location': 'Sunset District', 'start': 945, 'end': 1020, 'min_duration': 45},
        {'name': 'George', 'location': 'The Castro', 'start': 840, 'end': 975, 'min_duration': 75},
    ]

    travel_data = [
        ('Chinatown', 'Embarcadero', 5),
        ('Chinatown', 'Pacific Heights', 10),
        ('Chinatown', 'Russian Hill', 7),
        ('Chinatown', 'Haight-Ashbury', 19),
        ('Chinatown', 'Golden Gate Park', 23),
        ('Chinatown', 'Fisherman\'s Wharf', 8),
        ('Chinatown', 'Sunset District', 29),
        ('Chinatown', 'The Castro', 22),
        ('Embarcadero', 'Chinatown', 7),
        ('Embarcadero', 'Pacific Heights', 11),
        ('Embarcadero', 'Russian Hill', 8),
        ('Embarcadero', 'Haight-Ashbury', 21),
        ('Embarcadero', 'Golden Gate Park', 25),
        ('Embarcadero', 'Fisherman\'s Wharf', 6),
        ('Embarcadero', 'Sunset District', 30),
        ('Embarcadero', 'The Castro', 25),
        ('Pacific Heights', 'Chinatown', 11),
        ('Pacific Heights', 'Embarcadero', 10),
        ('Pacific Heights', 'Russian Hill', 7),
        ('Pacific Heights', 'Haight-Ashbury', 11),
        ('Pacific Heights', 'Golden Gate Park', 15),
        ('Pacific Heights', 'Fisherman\'s Wharf', 13),
        ('Pacific Heights', 'Sunset District', 21),
        ('Pacific Heights', 'The Castro', 16),
        ('Russian Hill', 'Chinatown', 9),
        ('Russian Hill', 'Embarcadero', 8),
        ('Russian Hill', 'Pacific Heights', 7),
        ('Russian Hill', 'Haight-Ashbury', 17),
        ('Russian Hill', 'Golden Gate Park', 21),
        ('Russian Hill', 'Fisherman\'s Wharf', 7),
        ('Russian Hill', 'Sunset District', 23),
        ('Russian Hill', 'The Castro', 21),
        ('Haight-Ashbury', 'Chinatown', 19),
        ('Haight-Ashbury', 'Embarcadero', 20),
        ('Haight-Ashbury', 'Pacific Heights', 12),
        ('Haight-Ashbury', 'Russian Hill', 17),
        ('Haight-Ashbury', 'Golden Gate Park', 7),
        ('Haight-Ashbury', 'Fisherman\'s Wharf', 23),
        ('Haight-Ashbury', 'Sunset District', 15),
        ('Haight-Ashbury', 'The Castro', 6),
        ('Golden Gate Park', 'Chinatown', 23),
        ('Golden Gate Park', 'Embarcadero', 25),
        ('Golden Gate Park', 'Pacific Heights', 16),
        ('Golden Gate Park', 'Russian Hill', 19),
        ('Golden Gate Park', 'Haight-Ashbury', 7),
        ('Golden Gate Park', 'Fisherman\'s Wharf', 24),
        ('Golden Gate Park', 'Sunset District', 10),
        ('Golden Gate Park', 'The Castro', 13),
        ('Fisherman\'s Wharf', 'Chinatown', 12),
        ('Fisherman\'s Wharf', 'Embarcadero', 8),
        ('Fisherman\'s Wharf', 'Pacific Heights', 12),
        ('Fisherman\'s Wharf', 'Russian Hill', 7),
        ('Fisherman\'s Wharf', 'Haight-Ashbury', 22),
        ('Fisherman\'s Wharf', 'Golden Gate Park', 25),
        ('Fisherman\'s Wharf', 'Sunset District', 27),
        ('Fisherman\'s Wharf', 'The Castro', 27),
        ('Sunset District', 'Chinatown', 30),
        ('Sunset District', 'Embarcadero', 30),
        ('Sunset District', 'Pacific Heights', 21),
        ('Sunset District', 'Russian Hill', 24),
        ('Sunset District', 'Haight-Ashbury', 15),
        ('Sunset District', 'Golden Gate Park', 11),
        ('Sunset District', 'Fisherman\'s Wharf', 29),
        ('Sunset District', 'The Castro', 17),
        ('The Castro', 'Chinatown', 22),
        ('The Castro', 'Embarcadero', 22),
        ('The Castro', 'Pacific Heights', 16),
        ('The Castro', 'Russian Hill', 18),
        ('The Castro', 'Haight-Ashbury', 6),
        ('The Castro', 'Golden Gate Park', 11),
        ('The Castro', 'Fisherman\'s Wharf', 24),
        ('The Castro', 'Sunset District', 17),
    ]

    travel_times = {}
    for from_loc, to_loc, time in travel_data:
        if from_loc not in travel_times:
            travel_times[from_loc] = {}
        travel_times[from_loc][to_loc] = time

    friend_vars = {}
    for friend in friends:
        name = friend['name']
        met = Bool(f'met_{name}')
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        loc = friend['location']
        friend_vars[name] = (met, start, end, loc)
        # Basic constraints if meeting
        opt.add(Implies(met, start >= friend['start']))
        opt.add(Implies(met, end <= friend['end']))
        opt.add(Implies(met, end >= start + friend['min_duration']))
        # Start time must be after arrival from Chinatown or another friend
        from_chinatown = 540 + travel_times['Chinatown'][loc]
        cond = Or(start >= from_chinatown)
        for other in friends:
            if other['name'] == name:
                continue
            other_met, other_start, other_end, other_loc = friend_vars[other['name']]
            cond = Or(cond, And(other_met, start >= other_end + travel_times[other_loc][loc]))
        opt.add(Implies(met, cond))

    # Pairwise non-overlap with travel time
    friend_names = [f['name'] for f in friends]
    for i in range(len(friend_names)):
        for j in range(i+1, len(friend_names)):
            a = friend_names[i]
            b = friend_names[j]
            met_a, start_a, end_a, loc_a = friend_vars[a]
            met_b, start_b, end_b, loc_b = friend_vars[b]
            time_ab = travel_times[loc_a][loc_b]
            time_ba = travel_times[loc_b][loc_a]
            opt.add(Implies(And(met_a, met_b),
                             Or(end_a + time_ab <= start_b,
                                end_b + time_ba <= start_a)))

    # Maximize number of friends met
    total = Sum([If(met, 1, 0) for met, _, _, _ in friend_vars.values()])
    opt.maximize(total)

    if opt.check() == sat:
        m = opt.model()
        count = 0
        for name in friend_names:
            met, start, end, _ = friend_vars[name]
            if m.eval(met):
                count +=1
                s = m.eval(start).as_long()
                e = m.eval(end).as_long()
                print(f"{name}: {s//60:02}:{s%60:02} to {e//60:02}:{e%60:02}")
        print(f"Total friends met: {count}")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()