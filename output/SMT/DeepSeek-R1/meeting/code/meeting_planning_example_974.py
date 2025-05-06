from z3 import *

def main():
    opt = Optimize()

    friends = [
        {'name': 'Charles', 'location': 'Presidio', 'start': 795, 'end': 900, 'min_duration': 105},
        {'name': 'Robert', 'location': 'Nob Hill', 'start': 795, 'end': 1050, 'min_duration': 90},
        {'name': 'Nancy', 'location': 'Pacific Heights', 'start': 885, 'end': 1320, 'min_duration': 105},
        {'name': 'Brian', 'location': 'Mission District', 'start': 930, 'end': 1320, 'min_duration': 60},
        {'name': 'Kimberly', 'location': 'Marina District', 'start': 1020, 'end': 1185, 'min_duration': 75},
        {'name': 'David', 'location': 'North Beach', 'start': 885, 'end': 990, 'min_duration': 75},
        {'name': 'William', 'location': 'Russian Hill', 'start': 750, 'end': 1155, 'min_duration': 120},
        {'name': 'Jeffrey', 'location': 'Richmond District', 'start': 720, 'end': 1155, 'min_duration': 45},
        {'name': 'Karen', 'location': 'Embarcadero', 'start': 855, 'end': 1245, 'min_duration': 60},
        {'name': 'Joshua', 'location': 'Alamo Square', 'start': 1125, 'end': 1320, 'min_duration': 60},
    ]

    travel_data = [
        ('Sunset District', 'Presidio', 16),
        ('Sunset District', 'Nob Hill', 27),
        ('Sunset District', 'Pacific Heights', 21),
        ('Sunset District', 'Mission District', 25),
        ('Sunset District', 'Marina District', 21),
        ('Sunset District', 'North Beach', 28),
        ('Sunset District', 'Russian Hill', 24),
        ('Sunset District', 'Richmond District', 12),
        ('Sunset District', 'Embarcadero', 30),
        ('Sunset District', 'Alamo Square', 17),
        ('Presidio', 'Sunset District', 15),
        ('Presidio', 'Nob Hill', 18),
        ('Presidio', 'Pacific Heights', 11),
        ('Presidio', 'Mission District', 26),
        ('Presidio', 'Marina District', 11),
        ('Presidio', 'North Beach', 18),
        ('Presidio', 'Russian Hill', 14),
        ('Presidio', 'Richmond District', 7),
        ('Presidio', 'Embarcadero', 20),
        ('Presidio', 'Alamo Square', 19),
        ('Nob Hill', 'Sunset District', 24),
        ('Nob Hill', 'Presidio', 17),
        ('Nob Hill', 'Pacific Heights', 8),
        ('Nob Hill', 'Mission District', 13),
        ('Nob Hill', 'Marina District', 11),
        ('Nob Hill', 'North Beach', 8),
        ('Nob Hill', 'Russian Hill', 5),
        ('Nob Hill', 'Richmond District', 14),
        ('Nob Hill', 'Embarcadero', 9),
        ('Nob Hill', 'Alamo Square', 11),
        ('Pacific Heights', 'Sunset District', 21),
        ('Pacific Heights', 'Presidio', 11),
        ('Pacific Heights', 'Nob Hill', 8),
        ('Pacific Heights', 'Mission District', 15),
        ('Pacific Heights', 'Marina District', 6),
        ('Pacific Heights', 'North Beach', 9),
        ('Pacific Heights', 'Russian Hill', 7),
        ('Pacific Heights', 'Richmond District', 12),
        ('Pacific Heights', 'Embarcadero', 10),
        ('Pacific Heights', 'Alamo Square', 10),
        ('Mission District', 'Sunset District', 24),
        ('Mission District', 'Presidio', 25),
        ('Mission District', 'Nob Hill', 12),
        ('Mission District', 'Pacific Heights', 16),
        ('Mission District', 'Marina District', 19),
        ('Mission District', 'North Beach', 17),
        ('Mission District', 'Russian Hill', 15),
        ('Mission District', 'Richmond District', 20),
        ('Mission District', 'Embarcadero', 19),
        ('Mission District', 'Alamo Square', 11),
        ('Marina District', 'Sunset District', 19),
        ('Marina District', 'Presidio', 10),
        ('Marina District', 'Nob Hill', 12),
        ('Marina District', 'Pacific Heights', 7),
        ('Marina District', 'Mission District', 20),
        ('Marina District', 'North Beach', 11),
        ('Marina District', 'Russian Hill', 8),
        ('Marina District', 'Richmond District', 11),
        ('Marina District', 'Embarcadero', 14),
        ('Marina District', 'Alamo Square', 15),
        ('North Beach', 'Sunset District', 27),
        ('North Beach', 'Presidio', 17),
        ('North Beach', 'Nob Hill', 7),
        ('North Beach', 'Pacific Heights', 8),
        ('North Beach', 'Mission District', 18),
        ('North Beach', 'Marina District', 9),
        ('North Beach', 'Russian Hill', 4),
        ('North Beach', 'Richmond District', 18),
        ('North Beach', 'Embarcadero', 6),
        ('North Beach', 'Alamo Square', 16),
        ('Russian Hill', 'Sunset District', 23),
        ('Russian Hill', 'Presidio', 14),
        ('Russian Hill', 'Nob Hill', 5),
        ('Russian Hill', 'Pacific Heights', 7),
        ('Russian Hill', 'Mission District', 16),
        ('Russian Hill', 'Marina District', 7),
        ('Russian Hill', 'North Beach', 5),
        ('Russian Hill', 'Richmond District', 14),
        ('Russian Hill', 'Embarcadero', 8),
        ('Russian Hill', 'Alamo Square', 15),
        ('Richmond District', 'Sunset District', 11),
        ('Richmond District', 'Presidio', 7),
        ('Richmond District', 'Nob Hill', 17),
        ('Richmond District', 'Pacific Heights', 10),
        ('Richmond District', 'Mission District', 20),
        ('Richmond District', 'Marina District', 9),
        ('Richmond District', 'North Beach', 17),
        ('Richmond District', 'Russian Hill', 13),
        ('Richmond District', 'Embarcadero', 19),
        ('Richmond District', 'Alamo Square', 13),
        ('Embarcadero', 'Sunset District', 30),
        ('Embarcadero', 'Presidio', 20),
        ('Embarcadero', 'Nob Hill', 10),
        ('Embarcadero', 'Pacific Heights', 11),
        ('Embarcadero', 'Mission District', 20),
        ('Embarcadero', 'Marina District', 12),
        ('Embarcadero', 'North Beach', 5),
        ('Embarcadero', 'Russian Hill', 8),
        ('Embarcadero', 'Richmond District', 21),
        ('Embarcadero', 'Alamo Square', 19),
        ('Alamo Square', 'Sunset District', 16),
        ('Alamo Square', 'Presidio', 17),
        ('Alamo Square', 'Nob Hill', 11),
        ('Alamo Square', 'Pacific Heights', 10),
        ('Alamo Square', 'Mission District', 10),
        ('Alamo Square', 'Marina District', 15),
        ('Alamo Square', 'North Beach', 15),
        ('Alamo Square', 'Russian Hill', 13),
        ('Alamo Square', 'Richmond District', 11),
        ('Alamo Square', 'Embarcadero', 16),
    ]

    travel_times = {}
    for from_loc, to_loc, time in travel_data:
        if from_loc not in travel_times:
            travel_times[from_loc] = {}
        travel_times[from_loc][to_loc] = time

    friend_vars = []
    for friend in friends:
        name = friend['name']
        met = Bool(f'met_{name}')
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        loc = friend['location']
        start_min = friend['start']
        end_max = friend['end']
        duration = friend['min_duration']
        # Constraints if meeting
        opt.add(Implies(met, start >= start_min))
        opt.add(Implies(met, end <= end_max))
        opt.add(Implies(met, end >= start + duration))
        # Start time must account for travel from Sunset District
        travel_from_sunset = travel_times['Sunset District'][loc]
        opt.add(Implies(met, start >= 540 + travel_from_sunset))
        friend_vars.append( (met, start, end, loc) )

    # Pairwise constraints for travel times
    for i in range(len(friend_vars)):
        for j in range(i+1, len(friend_vars)):
            met_i, start_i, end_i, loc_i = friend_vars[i]
            met_j, start_j, end_j, loc_j = friend_vars[j]
            time_ij = travel_times[loc_i][loc_j]
            time_ji = travel_times[loc_j][loc_i]
            opt.add(Implies(And(met_i, met_j),
                             Or(end_i + time_ij <= start_j,
                                end_j + time_ji <= start_i)))

    # Maximize number of friends met
    total = Sum([If(met, 1, 0) for met, _, _, _ in friend_vars])
    opt.maximize(total)

    if opt.check() == sat:
        m = opt.model()
        count = 0
        for met, _, _, name in friend_vars:
            if m.eval(met):
                count +=1
                start_val = m.eval(met.start)
                end_val = m.eval(met.end)
                print(f"{name}: {start_val//60:02}:{start_val%60:02} to {end_val//60:02}:{end_val%60:02}")
        print(f"Total friends met: {count}")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()