from z3 import *

def main():
    opt = Optimize()

    friends = [
        {'name': 'Start', 'location': 'Sunset District', 'start': 540, 'end': 540, 'min_duration': 0},
        {'name': 'Anthony', 'location': 'Chinatown', 'start': 795, 'end': 930, 'min_duration': 60},
        {'name': 'Rebecca', 'location': 'Russian Hill', 'start': 1140, 'end': 1290, 'min_duration': 105},
        {'name': 'Melissa', 'location': 'North Beach', 'start': 495, 'end': 810, 'min_duration': 105},
    ]

    travel_data = [
        ('Sunset District', 'Chinatown', 30),
        ('Sunset District', 'Russian Hill', 24),
        ('Sunset District', 'North Beach', 29),
        ('Chinatown', 'Sunset District', 29),
        ('Chinatown', 'Russian Hill', 7),
        ('Chinatown', 'North Beach', 3),
        ('Russian Hill', 'Sunset District', 23),
        ('Russian Hill', 'Chinatown', 9),
        ('Russian Hill', 'North Beach', 5),
        ('North Beach', 'Sunset District', 27),
        ('North Beach', 'Chinatown', 6),
        ('North Beach', 'Russian Hill', 4),
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
        
        if name == 'Start':
            opt.add(met == True)
            opt.add(start == 540)
            opt.add(end == 540)
        else:
            opt.add(Implies(met, start >= friend['start']))
            opt.add(Implies(met, end <= friend['end']))
            opt.add(Implies(met, end >= start + friend['min_duration']))

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

    total = Sum([If(met, 1, 0) for name in friend_names if name != 'Start' for met in [friend_vars[name][0]]])
    opt.maximize(total)

    if opt.check() == sat:
        m = opt.model()
        count = 0
        for name in friend_names:
            if name == 'Start':
                continue
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