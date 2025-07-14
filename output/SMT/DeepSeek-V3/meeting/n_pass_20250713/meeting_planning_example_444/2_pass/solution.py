from z3 import *

def solve_scheduling():
    # Initialize optimizer
    opt = Optimize()

    # Friends and their details
    friends = {
        'Ronald': {'location': 'Russian Hill', 'start': 13.75, 'end': 17.25, 'min_duration': 1.75, 'travel_from_fd': 10/60},
        'Patricia': {'location': 'Sunset District', 'start': 9.25, 'end': 22.0, 'min_duration': 1.0, 'travel_from_fd': 31/60},
        'Laura': {'location': 'North Beach', 'start': 12.5, 'end': 12.75, 'min_duration': 0.25, 'travel_from_fd': 7/60},
        'Emily': {'location': 'The Castro', 'start': 16.25, 'end': 18.5, 'min_duration': 1.0, 'travel_from_fd': 23/60},
        'Mary': {'location': 'Golden Gate Park', 'start': 15.0, 'end': 16.5, 'min_duration': 1.0, 'travel_from_fd': 23/60}
    }

    # Travel times dictionary (simplified for this problem)
    travel_times = {
        ('Financial District', 'Russian Hill'): 10/60,
        ('Financial District', 'Sunset District'): 31/60,
        ('Financial District', 'North Beach'): 7/60,
        ('Financial District', 'The Castro'): 23/60,
        ('Financial District', 'Golden Gate Park'): 23/60,
        ('Russian Hill', 'Sunset District'): 23/60,
        ('Russian Hill', 'North Beach'): 5/60,
        ('Russian Hill', 'The Castro'): 21/60,
        ('Russian Hill', 'Golden Gate Park'): 21/60,
        ('Sunset District', 'Russian Hill'): 24/60,
        ('Sunset District', 'North Beach'): 29/60,
        ('Sunset District', 'The Castro'): 17/60,
        ('Sunset District', 'Golden Gate Park'): 11/60,
        ('North Beach', 'Russian Hill'): 4/60,
        ('North Beach', 'Sunset District'): 27/60,
        ('North Beach', 'The Castro'): 22/60,
        ('North Beach', 'Golden Gate Park'): 22/60,
        ('The Castro', 'Russian Hill'): 18/60,
        ('The Castro', 'Sunset District'): 17/60,
        ('The Castro', 'North Beach'): 20/60,
        ('The Castro', 'Golden Gate Park'): 11/60,
        ('Golden Gate Park', 'Russian Hill'): 19/60,
        ('Golden Gate Park', 'Sunset District'): 10/60,
        ('Golden Gate Park', 'North Beach'): 24/60,
        ('Golden Gate Park', 'The Castro'): 13/60,
    }

    # Variables for each friend: start time, end time, and whether they are met
    met = {}
    start = {}
    end = {}
    for name in friends:
        met[name] = Bool(name)
        start[name] = Real(f'start_{name}')
        end[name] = Real(f'end_{name}')

    # Current location starts at Financial District
    current_location = 'Financial District'
    arrival_time = 9.0  # 9:00 AM

    # Constraints for each friend
    for name in friends:
        data = friends[name]
        # If the friend is met, their meeting must fit within their window and duration
        opt.add(Implies(met[name], start[name] >= data['start']))
        opt.add(Implies(met[name], end[name] <= data['end']))
        opt.add(Implies(met[name], end[name] - start[name] >= data['min_duration']))

    # Ensure no overlapping meetings and travel time between consecutive meetings
    names = list(friends.keys())
    for i in range(len(names)):
        for j in range(i+1, len(names)):
            name1 = names[i]
            name2 = names[j]
            loc1 = friends[name1]['location']
            loc2 = friends[name2]['location']
            travel = travel_times.get((loc1, loc2), travel_times.get((loc2, loc1), 0))
            opt.add(Implies(And(met[name1], met[name2]),
                          Or(end[name1] + travel <= start[name2],
                             end[name2] + travel <= start[name1])))

    # Also, the first meeting must be after arrival_time + travel from Financial District
    for name in friends:
        travel_time = friends[name]['travel_from_fd']
        opt.add(Implies(met[name], start[name] >= arrival_time + travel_time))

    # Objective: maximize the number of friends met
    total_met = Sum([If(met[name], 1, 0) for name in friends])
    opt.maximize(total_met)

    # Additional constraint: exactly 4 friends must be met
    opt.add(total_met == 4)

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        print("Optimal Schedule (Meeting exactly 4 friends):")
        scheduled = []
        for name in friends:
            if is_true(m[met[name]]):
                start_val = m[start[name]]
                end_val = m[end[name]]
                start_hour = float(start_val.numerator_as_long())/float(start_val.denominator_as_long())
                end_hour = float(end_val.numerator_as_long())/float(end_val.denominator_as_long())
                start_time = f"{int(start_hour)}:{int((start_hour % 1) * 60):02d}"
                end_time = f"{int(end_hour)}:{int((end_hour % 1) * 60):02d}"
                scheduled.append((name, start_time, end_time))
        scheduled.sort(key=lambda x: x[1])  # sort by start time
        for meet in scheduled:
            print(f"Meet {meet[0]} from {meet[1]} to {meet[2]}")
        print(f"Total friends met: {len(scheduled)}")
    else:
        print("No feasible schedule found that meets exactly 4 friends.")

solve_scheduling()