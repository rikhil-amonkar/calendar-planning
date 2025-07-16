from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and friends
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

    # Friends' data: name, location, available start, available end, min duration
    friends = [
        ('Joseph', 1, 8*60, 17.5*60, 90),
        ('Jeffrey', 2, 17.5*60, 21.5*60, 60),
        ('Kevin', 3, 11.25*60, 15.25*60, 30),
        ('David', 4, 8.25*60, 9*60, 30),
        ('Barbara', 5, 10.5*60, 16.5*60, 15)
    ]

    # Variables for each friend: start time and end time of meeting
    start_vars = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    end_vars = [Int(f'end_{name}') for name, _, _, _, _ in friends]

    # Arrival time at Golden Gate Park is 9:00 AM (540 minutes)
    current_time = 540
    current_location = locations['Golden_Gate_Park']

    # Constraints for each friend
    for i, (name, loc, avail_start, avail_end, min_dur) in enumerate(friends):
        s.add(start_vars[i] >= avail_start)
        s.add(end_vars[i] <= avail_end)
        s.add(end_vars[i] == start_vars[i] + min_dur)

        # Travel time from current location to friend's location
        if i == 0:
            # First meeting: travel from Golden Gate Park
            travel_time = travel_times[current_location][loc]
            s.add(start_vars[i] >= current_time + travel_time)
        else:
            # Subsequent meetings: travel from previous location
            prev_loc = friends[i-1][1]
            travel_time = travel_times[prev_loc][loc]
            s.add(start_vars[i] >= end_vars[i-1] + travel_time)

    # Ensure no overlapping meetings (though travel times should prevent this)
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            s.add(Or(
                end_vars[i] + travel_times[friends[i][1]][friends[j][1]] <= start_vars[j],
                end_vars[j] + travel_times[friends[j][1]][friends[i][1]] <= start_vars[i]
            ))

    # Try to meet as many friends as possible
    # We can add a variable to indicate if a friend is met
    met = [Bool(f'met_{name}') for name, _, _, _, _ in friends]
    for i in range(len(friends)):
        s.add(met[i] == (start_vars[i] >= 0))

    # Maximize the number of friends met
    s.maximize(Sum([If(met[i], 1, 0) for i in range(len(friends))]))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        for i, (name, _, _, _, _) in enumerate(friends):
            if m.evaluate(met[i]):
                start = m.evaluate(start_vars[i]).as_long()
                end = m.evaluate(end_vars[i]).as_long()
                print(f"Meet {name} from {start//60}:{start%60:02d} to {end//60}:{end%60:02d}")
            else:
                print(f"Cannot meet {name}")
    else:
        print("No solution found")

solve_scheduling()