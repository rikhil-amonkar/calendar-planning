from z3 import *

def main():
    # Define travel_time dictionary with all 42 entries
    travel_time = {
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Nob Hill'): 7,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Mission District'): 18,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Nob Hill'): 8,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Nob Hill'): 9,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Nob Hill'): 12,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Golden Gate Park'): 17
    }

    # Friends data: (name, location, window_start (min), window_end (min), min_duration (min))
    friends = [
        ('James', 'Pacific Heights', 660, 780, 120),
        ('Robert', 'Chinatown', 195, 465, 90),
        ('Jeffrey', 'Union Square', 30, 390, 120),
        ('Carol', 'Mission District', 555, 735, 15),
        ('Mark', 'Golden Gate Park', 150, 525, 15),
        ('Sandra', 'Nob Hill', 0, 390, 15)
    ]

    # Create Z3 optimizer
    optimizer = Optimize()

    n_friends = len(friends)
    n_meetings = n_friends + 1  # including virtual meeting at index0

    # Locations for meetings: index0 is virtual meeting at North Beach
    locs = ['North Beach']  # meeting0 location
    for i in range(n_friends):
        locs.append(friends[i][1])

    # Arrays for variables: index 0 is virtual meeting (fixed), indices 1..6 for friends
    meet = [None] * n_meetings   # meet[0] is virtual and always true, but we don't need a variable for it
    start = [None] * n_meetings
    end = [None] * n_meetings

    # Virtual meeting at index 0
    start[0] = 0
    end[0] = 0

    # Create variables for friends (indices 1 to 6)
    for i in range(1, n_meetings):
        meet[i] = Bool(f'meet_{i}')
        start[i] = Int(f'start_{i}')
        end[i] = Int(f'end_{i}')

    # Constraints for each friend
    for i in range(1, n_meetings):
        name, loc, ws, we, dur = friends[i-1]
        # If we meet this friend, then the meeting must be within the window and have the minimum duration
        optimizer.add(Implies(meet[i], And(
            start[i] >= ws,
            end[i] == start[i] + dur,
            end[i] <= we
        )))

    # Constraints for travel from North Beach (virtual meeting) to each friend
    for i in range(1, n_meetings):
        time_0i = travel_time[(locs[0], locs[i])]
        optimizer.add(Implies(meet[i], start[i] >= time_0i))

    # Constraints for every pair of friends (i, j) where i < j
    for i in range(1, n_meetings):
        for j in range(i+1, n_meetings):
            time_ij = travel_time[(locs[i], locs[j])]
            time_ji = travel_time[(locs[j], locs[i])]
            # If both meetings are held, then either i comes before j or j comes before i with travel time
            optimizer.add(Implies(And(meet[i], meet[j]), 
                          Or(start[j] >= end[i] + time_ij, 
                             start[i] >= end[j] + time_ji)))

    # Objective: maximize the number of friends met
    objective = Sum([If(meet[i], 1, 0) for i in range(1, n_meetings)])
    optimizer.maximize(objective)

    # Check and get the solution
    if optimizer.check() == sat:
        model = optimizer.model()
        print("SOLUTION:")
        total_met = 0
        schedule = []
        for i in range(1, n_meetings):
            if is_true(model.eval(meet[i])):
                total_met += 1
                s_val = model.eval(start[i]).as_long()
                e_val = model.eval(end[i]).as_long()
                name = friends[i-1][0]
                schedule.append((name, s_val, e_val))
        print(f"Total friends met: {total_met}")
        for name, start_val, end_val in schedule:
            # Convert minutes back to time string
            start_hour = 9 + (start_val // 60)
            start_minute = start_val % 60
            end_hour = 9 + (end_val // 60)
            end_minute = end_val % 60
            start_str = f"{start_hour}:{start_minute:02d}"
            end_str = f"{end_hour}:{end_minute:02d}"
            print(f"Meet {name} from {start_str} to {end_str}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()