from z3 import *

def solve_scheduling():
    # Initialize optimizer
    opt = Optimize()

    # Define friends and their details
    friends = {
        'Jeffrey': {'location': 'Fisherman\'s Wharf', 'start': 10.25, 'end': 13.0, 'min_duration': 1.5},
        'Ronald': {'location': 'Alamo Square', 'start': 7.75, 'end': 14.75, 'min_duration': 2.0},
        'Jason': {'location': 'Financial District', 'start': 10.75, 'end': 16.0, 'min_duration': 1.75},
        'Melissa': {'location': 'Union Square', 'start': 17.75, 'end': 18.25, 'min_duration': 0.25},
        'Elizabeth': {'location': 'Sunset District', 'start': 14.75, 'end': 17.5, 'min_duration': 1.75},
        'Margaret': {'location': 'Embarcadero', 'start': 13.25, 'end': 19.0, 'min_duration': 1.5},
        'George': {'location': 'Golden Gate Park', 'start': 19.0, 'end': 22.0, 'min_duration': 1.25},
        'Richard': {'location': 'Chinatown', 'start': 9.5, 'end': 21.0, 'min_duration': 0.25},
        'Laura': {'location': 'Richmond District', 'start': 9.75, 'end': 18.0, 'min_duration': 1.0}
    }

    # Define travel times (in hours)
    travel_times = {
        ('Alamo Square', 'Financial District'): 17/60,
        # ... (other travel times remain the same)
    }

    # Create variables
    meeting_start = {name: Real(f'start_{name}') for name in friends}
    meeting_end = {name: Real(f'end_{name}') for name in friends}
    met = [Bool(f'met_{name}') for name in friends]

    # Constraints
    for name in friends:
        friend = friends[name]
        opt.add(Implies(met[list(friends.keys()).index(name)],
                       And(meeting_start[name] >= friend['start'],
                           meeting_end[name] <= friend['end'],
                           meeting_end[name] - meeting_start[name] >= friend['min_duration'])))

    # Order constraints with proper travel times
    friend_names = list(friends.keys())
    for i in range(len(friend_names)):
        for j in range(i + 1, len(friend_names)):
            name1 = friend_names[i]
            name2 = friend_names[j]
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            travel_time = travel_times.get((loc1, loc2), 0)
            opt.add(Implies(And(met[i], met[j]),
                           Or(meeting_end[name1] + travel_time <= meeting_start[name2],
                              meeting_end[name2] + travel_time <= meeting_start[name1])))

    # Starting constraints
    for name in friends:
        loc = friends[name]['location']
        travel_time = travel_times.get(('Presidio', loc), 0)
        opt.add(Implies(met[list(friends.keys()).index(name)],
                       meeting_start[name] >= 9.0 + travel_time))

    # Must meet exactly 7 friends
    opt.add(Sum([If(m, 1, 0) for m in met]) == 7)

    # Solve
    if opt.check() == sat:
        model = opt.model()
        print("Valid Schedule (meeting exactly 7 friends with proper travel times):")
        schedule = []
        for name in friends:
            if is_true(model[met[list(friends.keys()).index(name)]]):
                start = float(model[meeting_start[name]].as_fraction())
                end = float(model[meeting_end[name]].as_fraction())
                schedule.append((name, friends[name]['location'], start, end))
        
        # Sort and print schedule
        schedule.sort(key=lambda x: x[2])
        for name, loc, start, end in schedule:
            print(f"Meet {name} at {loc} from {start:.2f} to {end:.2f}")
            
            # Verify travel times
            idx = schedule.index((name, loc, start, end))
            if idx > 0:
                prev_name, prev_loc, prev_start, prev_end = schedule[idx-1]
                travel = travel_times.get((prev_loc, loc), 0)
                actual_gap = start - prev_end
                print(f"  Travel from {prev_loc} to {loc}: needs {travel*60:.0f} min, has {actual_gap*60:.0f} min")
    else:
        print("No valid schedule found that meets all constraints.")

solve_scheduling()