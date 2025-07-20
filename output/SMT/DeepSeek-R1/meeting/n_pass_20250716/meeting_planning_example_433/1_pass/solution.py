from z3 import *

def main():
    # Define events: 0 = start (Nob Hill), 1=Emily, 2=Margaret, 3=Ronald, 4=Deborah, 5=Jeffrey
    n_friends = 5
    n_events = n_friends + 1  # including start

    # Meet variables for friends (events 1 to 5)
    meet = [Bool(f'meet_{i+1}') for i in range(n_friends)]
    
    # Start time variables for all events (0 to 5)
    s = [Int(f's_{i}') for i in range(n_events)]
    
    # Duration for each event (0 for start, then min durations for friends)
    dur = [0, 15, 75, 45, 90, 120]  # index 0 to 5
    
    # Available time windows (in minutes from 9:00 AM)
    avail_start = [0, 600, 450, 570, 285, 135]  # event0 not used, but we have for 1-5: index1 to 5
    avail_end = [0, 720, 675, 630, 735, 330]    # same as above

    # Locations for events
    locs = {
        0: 'Nob Hill',
        1: 'Richmond District',
        2: 'Financial District',
        3: 'North Beach',
        4: 'The Castro',
        5: 'Golden Gate Park'
    }
    
    # Travel time dictionary
    travel_dict = {
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Golden Gate Park'): 17,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'The Castro'): 16,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Financial District', 'Nob Hill'): 8,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'The Castro'): 23,
        ('Financial District', 'Golden Gate Park'): 23,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'The Castro'): 22,
        ('North Beach', 'Golden Gate Park'): 22,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Richmond District'): 16,
        ('The Castro', 'Financial District'): 20,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Golden Gate Park'): 11,
        ('Golden Gate Park', 'Nob Hill'): 20,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'North Beach'): 24,
        ('Golden Gate Park', 'The Castro'): 13
    }
    
    # Build travel time matrix T: T[i][j] = travel time from locs[i] to locs[j]
    T = [[0] * n_events for _ in range(n_events)]
    for i in range(n_events):
        for j in range(n_events):
            if i == j:
                T[i][j] = 0
            else:
                from_loc = locs[i]
                to_loc = locs[j]
                T[i][j] = travel_dict[(from_loc, to_loc)]
    
    # Initialize solver
    solver = Solver()
    
    # Constraint: start event at time 0
    solver.add(s[0] == 0)
    
    # Constraints for each friend event
    for i in range(1, n_events):  # i from 1 to 5
        # If we meet friend i, then the meeting must be within their window
        solver.add(Implies(meet[i-1], s[i] >= avail_start[i]))
        solver.add(Implies(meet[i-1], s[i] + dur[i] <= avail_end[i]))
    
    # Constraints for disjunctive travel for every pair of distinct events (including start)
    for i in range(n_events):
        for j in range(i+1, n_events):  # j > i to avoid duplicates
            if i == 0:  # start event is always met
                cond = meet[j-1]  # condition: if friend j is met
            else:
                cond = And(meet[i-1], meet[j-1])  # condition: both friends i and j are met
            
            # Disjunctive constraint: 
            #   either event j starts after event i ends plus travel time from i to j, 
            #   or event i starts after event j ends plus travel time from j to i.
            option1 = (s[i] + dur[i] + T[i][j] <= s[j])
            option2 = (s[j] + dur[j] + T[j][i] <= s[i])
            solver.add(Implies(cond, Or(option1, option2)))
    
    # Objective: maximize the number of friends met
    num_meet = Sum([If(meet_i, 1, 0) for meet_i in meet])
    solver.maximize(num_meet)
    
    # Solve and output
    if solver.check() == sat:
        model = solver.model()
        total_met = model.evaluate(num_meet)
        print(f"SOLUTION: We can meet {total_met} friends.")
        friend_names = {
            1: 'Emily',
            2: 'Margaret',
            3: 'Ronald',
            4: 'Deborah',
            5: 'Jeffrey'
        }
        for i in range(n_friends):
            if model.evaluate(meet[i]):
                event_idx = i+1
                start_time = model.evaluate(s[event_idx])
                if isinstance(start_time, IntNumRef):
                    start_val = start_time.as_long()
                    hours = start_val // 60
                    minutes = start_val % 60
                    total_hours = 9 + hours
                    hour_in_12 = total_hours % 12
                    if hour_in_12 == 0:
                        hour_in_12 = 12
                    period = "AM" if total_hours < 12 else "PM"
                    # Adjust for 12 PM
                    if total_hours >= 12 and total_hours < 13:
                        period = "PM"
                    elif total_hours >= 13:
                        hour_in_12 = hour_in_12 if hour_in_12 != 0 else 12
                    print(f"Meet {friend_names[event_idx]} at {hour_in_12}:{minutes:02d} {period} for {dur[event_idx]} minutes.")
                else:
                    print(f"Meet {friend_names[event_idx]} at time {start_time} (model output not integer)")
            else:
                print(f"Cannot meet {friend_names[i+1]}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()