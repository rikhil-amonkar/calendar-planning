from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define locations with indices
    locations = {
        'Golden_Gate_Park': 0,
        'Fishermans_Wharf': 1,
        'Bayview': 2,
        'Mission_District': 3,
        'Embarcadero': 4,
        'Financial_District': 5
    }

    # Travel times matrix (minutes)
    travel = [
        [0, 24, 23, 17, 25, 26],  # Golden_Gate_Park
        [25, 0, 26, 22, 8, 11],    # Fishermans_Wharf
        [22, 25, 0, 13, 19, 19],   # Bayview
        [17, 22, 15, 0, 19, 17],   # Mission_District
        [25, 6, 21, 20, 0, 5],     # Embarcadero
        [23, 10, 19, 17, 4, 0]     # Financial_District
    ]

    # Friends data: name, location, available start, end, min duration (all in minutes)
    friends = [
        ('Joseph', 1, 8*60, 17.5*60, 90),
        ('Jeffrey', 2, 17.5*60, 21.5*60, 60),
        ('Kevin', 3, 11.25*60, 15.25*60, 30),
        ('David', 4, 8.25*60, 9*60, 30),
        ('Barbara', 5, 10.5*60, 16.5*60, 15)
    ]

    # Create variables
    meets = [Bool(f'meet_{name}') for name, _, _, _, _ in friends]
    starts = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    ends = [Int(f'end_{name}') for name, _, _, _, _ in friends]

    # Current time starts at 9:00 AM (540 minutes) at Golden Gate Park
    current_time = 540
    current_loc = locations['Golden_Gate_Park']

    # Add constraints for each friend
    for i, (name, loc, avail_start, avail_end, dur) in enumerate(friends):
        # If meeting this friend
        s.add(Implies(meets[i], starts[i] >= avail_start))
        s.add(Implies(meets[i], ends[i] <= avail_end))
        s.add(Implies(meets[i], ends[i] == starts[i] + dur))

        # If not meeting this friend
        s.add(Implies(Not(meets[i]), starts[i] == -1))
        s.add(Implies(Not(meets[i]), ends[i] == -1))

        # Travel time constraints
        if i == 0:
            s.add(Implies(meets[i], starts[i] >= current_time + travel[current_loc][loc]))
        else:
            for j in range(i):
                s.add(Implies(And(meets[j], meets[i]),
                            starts[i] >= ends[j] + travel[friends[j][1]][loc]))

    # No overlapping meetings
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            s.add(Implies(And(meets[i], meets[j]),
                         Or(ends[i] + travel[friends[i][1]][friends[j][1]] <= starts[j],
                            ends[j] + travel[friends[j][1]][friends[i][1]] <= starts[i])))

    # Maximize number of friends met
    s.maximize(Sum([If(meets[i], 1, 0) for i in range(len(friends))]))

    # Solve and print results
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        for i, (name, _, _, _, _) in enumerate(friends):
            if is_true(m.evaluate(meets[i])):
                start = m.evaluate(starts[i]).as_long()
                end = m.evaluate(ends[i]).as_long()
                print(f"Meet {name} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
            else:
                print(f"Cannot meet {name}")
    else:
        print("No valid schedule found")

solve_scheduling()