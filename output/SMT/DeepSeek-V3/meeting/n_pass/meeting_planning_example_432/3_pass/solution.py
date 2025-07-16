from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Optimize()

    # Define locations
    locations = {
        'Golden_Gate_Park': 0,
        'Fishermans_Wharf': 1,
        'Bayview': 2,
        'Mission_District': 3,
        'Embarcadero': 4,
        'Financial_District': 5
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 24, 23, 17, 25, 26],  # Golden_Gate_Park
        [25, 0, 26, 22, 8, 11],    # Fishermans_Wharf
        [22, 25, 0, 13, 19, 19],   # Bayview
        [17, 22, 15, 0, 19, 17],   # Mission_District
        [25, 6, 21, 20, 0, 5],     # Embarcadero
        [23, 10, 19, 17, 4, 0]     # Financial_District
    ]

    # Friends' data: name, location, available start (min), available end (min), min duration (min)
    friends = [
        ('Joseph', 1, 8*60, 17.5*60, 90),
        ('Jeffrey', 2, 17.5*60, 21.5*60, 60),
        ('Kevin', 3, 11.25*60, 15.25*60, 30),
        ('David', 4, 8.25*60, 9*60, 30),
        ('Barbara', 5, 10.5*60, 16.5*60, 15)
    ]

    # Create variables for meeting times
    start_times = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_times = [Int(f'end_{name}') for name, _, _, _, _ in friends]
    meet_flags = [Bool(f'meet_{name}') for name, _, _, _, _ in friends]

    # Arrival time at Golden Gate Park is 9:00 AM (540 minutes)
    current_time = 540
    current_loc = locations['Golden_Gate_Park']

    # Add constraints for each friend
    for i, (name, loc, avail_start, avail_end, min_dur) in enumerate(friends):
        # If we meet this friend
        s.add(Implies(meet_flags[i], start_times[i] >= avail_start))
        s.add(Implies(meet_flags[i], end_times[i] <= avail_end))
        s.add(Implies(meet_flags[i], end_times[i] == start_times[i] + min_dur))

        # If we don't meet this friend
        s.add(Implies(Not(meet_flags[i]), start_times[i] == -1))
        s.add(Implies(Not(meet_flags[i]), end_times[i] == -1))

        # Travel time constraints
        if i == 0:
            # First meeting: travel from Golden Gate Park
            s.add(Implies(meet_flags[i], 
                         start_times[i] >= current_time + travel_times[current_loc][loc]))
        else:
            # Subsequent meetings
            for j in range(i):
                s.add(Implies(And(meet_flags[j], meet_flags[i]),
                            start_times[i] >= end_times[j] + travel_times[friends[j][1]][loc]))

    # No overlapping meetings
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            s.add(Implies(And(meet_flags[i], meet_flags[j]),
                         Or(end_times[i] + travel_times[friends[i][1]][friends[j][1]] <= start_times[j],
                            end_times[j] + travel_times[friends[j][1]][friends[i][1]] <= start_times[i])))

    # Maximize the number of friends met
    s.maximize(Sum([If(meet_flags[i], 1, 0) for i in range(len(friends))]))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        for i, (name, _, _, _, _) in enumerate(friends):
            if is_true(m.evaluate(meet_flags[i])):
                start = m.evaluate(start_times[i]).as_long()
                end = m.evaluate(end_times[i]).as_long()
                print(f"Meet {name} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
            else:
                print(f"Cannot meet {name}")
    else:
        print("No solution found")

solve_scheduling()