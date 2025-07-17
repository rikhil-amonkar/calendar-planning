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

    # Create Z3 solver
    solver = Solver()

    # We have 6 friends (indices 1 to 6) and a virtual meeting at index 0 (North Beach, start=0, end=0)
    n_friends = len(friends)
    n_meetings = n_friends + 1  # including virtual meeting

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
        start[i] = Real(f'start_{i}')
        end[i] = Real(f'end_{i}')

    # Constraints for each friend
    for i in range(1, n_meetings):
        name, loc, ws, we, dur = friends[i-1]
        # If we meet this friend, then the meeting must be within the window and have the minimum duration
        solver.add(Implies(meet[i], And(
            start[i] >= ws,
            end[i] == start[i] + dur,
            end[i] <= we
        )))

    # Constraints from virtual meeting to each friend
    for j in range(1, n_meetings):
        _, loc_j, _, _, _ = friends[j-1]
        time_0j = travel_time[('North Beach', loc_j)]
        # If meeting j is held, then start[j] must be at least travel time from North Beach
        solver.add(Implies(meet[j], start[j] >= time_0j))

    # Constraints for every pair of friends (i, j) where i < j
    for i in range(1, n_meetings):
        for j in range(i+1, n_meetings):
            _, loc_i, _, _, _ = friends[i-1]
            _, loc_j, _, _, _ = friends[j-1]
            time_ij = travel_time[(loc_i, loc_j)]
            time_ji = travel_time[(loc_j, loc_i)]
            # If both meetings are held, then either i comes before j or j comes before i with travel time
            solver.add(Implies(And(meet[i], meet[j]), 
                          Or(start[j] >= end[i] + time_ij, 
                             start[i] >= end[j] + time_ji)))

    # Objective: maximize the number of friends met
    objective = Sum([If(meet[i], 1, 0) for i in range(1, n_meetings)])
    solver.maximize(objective)

    # Check and get the solution
    if solver.check() == sat:
        model = solver.model()
        print("SOLUTION:")
        total_met = 0
        schedule = []
        for i in range(1, n_meetings):
            if is_true(model.eval(meet[i])):
                total_met += 1
                s_val = model.eval(start[i])
                e_val = model.eval(end[i])
                name = friends[i-1][0]
                schedule.append((name, s_val, e_val))
        print(f"Total friends met: {total_met}")
        for name, start_val, end_val in schedule:
            # Convert minutes back to time string
            start_hour = 9 + (start_val.as_long() // 60)
            start_minute = start_val.as_long() % 60
            end_hour = 9 + (end_val.as_long() // 60)
            end_minute = end_val.as_long() % 60
            start_str = f"{start_hour}:{start_minute:02d}"
            end_str = f"{end_hour}:{end_minute:02d}"
            print(f"Meet {name} from {start_str} to {end_str}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()