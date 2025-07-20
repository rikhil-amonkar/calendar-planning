from z3 import *

def main():
    # Define locations and their indices
    locations = [
        'Presidio',
        'Golden Gate Park',    # Michelle
        'Fisherman\'s Wharf',  # Emily
        'Marina District',     # Mark
        'Alamo Square',        # Barbara
        'Sunset District',     # Laura
        'Nob Hill',            # Mary
        'North Beach'          # Helen
    ]
    n = len(locations)

    # Travel time matrix (travel[from_index][to_index] in minutes)
    travel = [
        [0, 12, 19, 11, 19, 15, 18, 18],   # Presidio
        [11, 0, 24, 16, 9, 10, 20, 23],    # Golden Gate Park
        [17, 25, 0, 9, 21, 27, 11, 6],     # Fisherman's Wharf
        [10, 18, 10, 0, 15, 19, 12, 11],   # Marina District
        [17, 9, 19, 15, 0, 16, 11, 15],    # Alamo Square
        [16, 11, 29, 21, 17, 0, 27, 28],   # Sunset District
        [17, 17, 10, 11, 11, 24, 0, 8],    # Nob Hill
        [17, 22, 5, 9, 16, 27, 7, 0]       # North Beach
    ]

    # Duration for each friend (0 for the dummy start at Presidio)
    durations = {
        0: 0,   # Dummy (Presidio)
        1: 15,  # Michelle
        2: 30,  # Emily
        3: 75,  # Mark
        4: 120, # Barbara
        5: 75,  # Laura
        6: 45,  # Mary
        7: 45   # Helen
    }

    # Availability windows (start, end) in minutes from 9:00 AM
    windows = {
        1: (660, 720),  # Michelle: 8:00 PM to 9:00 PM
        2: (435, 600),  # Emily: 4:15 PM to 7:00 PM
        3: (555, 645),  # Mark: 6:15 PM to 7:45 PM
        4: (480, 600),  # Barbara: 5:00 PM to 7:00 PM
        5: (600, 735),  # Laura: 7:00 PM to 9:15 PM
        6: (510, 600),  # Mary: 5:30 PM to 7:00 PM
        7: (120, 195)   # Helen: 11:00 AM to 12:15 PM
    }

    # Create solver
    s = Optimize()

    # Meet variables for friends (indices 1 to 7)
    meet = [Bool(f"meet_{i}") for i in range(1, 8)]
    meet_all = [True]  # meet_all[0] for dummy (always True)
    meet_all.extend(meet)  # meet_all[i] for location i (0 to 7)

    # Start time variables for all locations (0 to 7)
    start = [Int(f"start_{i}") for i in range(8)]
    s.add(start[0] == 0)  # Start at Presidio at time 0

    # Window constraints for friends
    for i in range(1, 8):
        s.add(Implies(meet_all[i], start[i] >= windows[i][0]))
        s.add(Implies(meet_all[i], start[i] + durations[i] <= windows[i][1]))

    # Ordering variables and constraints for all pairs (i, j) with i < j
    pairs = []
    b_vars = {}
    for i in range(n):
        for j in range(i + 1, n):
            pairs.append((i, j))
            b_vars[(i, j)] = Bool(f"b_{i}_{j}")

    for i, j in pairs:
        both_met = And(meet_all[i], meet_all[j])
        # If i before j
        before = And(b_vars[(i, j)], start[j] >= start[i] + durations[i] + travel[i][j])
        # If j before i
        after = And(Not(b_vars[(i, j)]), start[i] >= start[j] + durations[j] + travel[j][i])
        s.add(Implies(both_met, Or(before, after)))

    # Maximize the number of meetings
    total_meet = Sum([If(meet_all[i], 1, 0) for i in range(1, 8)])
    s.maximize(total_meet)

    # Solve
    if s.check() == sat:
        m = s.model()
        total = m.eval(total_meet)
        # Collect scheduled meetings
        scheduled = []
        for i in range(1, 8):
            if is_true(m.eval(meet_all[i])):
                start_time = m.eval(start[i])
                if isinstance(start_time, IntNumRef):
                    start_min = start_time.as_long()
                    hours = start_min // 60
                    mins = start_min % 60
                    time_str = f"{9 + hours}:{mins:02d}"
                    scheduled.append((start_min, locations[i], durations[i], time_str))
        # Sort by start time
        scheduled.sort()
        # Print schedule
        print("SOLUTION:")
        print(f"Total meetings: {total}")
        for meet in scheduled:
            print(f"Meet at {meet[1]} starting at {meet[3]} for {meet[2]} minutes")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()