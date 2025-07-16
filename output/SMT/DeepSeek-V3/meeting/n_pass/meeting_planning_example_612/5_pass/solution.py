from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Location indices and names
    locations = {
        'Alamo Square': 0,
        'Russian Hill': 1,
        'Presidio': 2,
        'Chinatown': 3,
        'Sunset District': 4,
        'The Castro': 5,
        'Embarcadero': 6,
        'Golden Gate Park': 7
    }

    # Travel times matrix (minutes)
    travel_times = [
        [0, 13, 18, 16, 16, 8, 17, 9],    # Alamo Square
        [15, 0, 14, 9, 23, 21, 8, 21],    # Russian Hill
        [18, 14, 0, 21, 15, 21, 20, 12],  # Presidio
        [17, 7, 19, 0, 29, 22, 5, 23],    # Chinatown
        [17, 24, 16, 30, 0, 17, 31, 11],  # Sunset District
        [8, 18, 20, 20, 17, 0, 22, 11],   # The Castro
        [19, 8, 20, 7, 30, 25, 0, 25],    # Embarcadero
        [10, 19, 11, 23, 10, 13, 25, 0]   # Golden Gate Park
    ]

    # Friends data: name, location, start (minutes), end (minutes), min_duration
    friends = [
        ('Emily', 'Russian Hill', 735, 855, 105),    # 12:15-14:15
        ('Mark', 'Presidio', 885, 1170, 60),        # 14:45-19:30
        ('Deborah', 'Chinatown', 450, 930, 45),     # 7:30-15:30
        ('Margaret', 'Sunset District', 1290, 1350, 60),  # 21:30-22:30
        ('George', 'The Castro', 450, 855, 60),     # 7:30-14:15
        ('Andrew', 'Embarcadero', 1215, 1320, 75),  # 20:15-22:00
        ('Steven', 'Golden Gate Park', 675, 1275, 105)   # 11:15-21:15
    ]

    # Current location and time
    current_time = 540  # 9:00 AM in minutes
    current_loc = locations['Alamo Square']

    # Create meeting variables
    meet_starts = [Int(f'start_{i}') for i in range(len(friends))]
    meet_ends = [Int(f'end_{i}') for i in range(len(friends))]
    meet_locs = [locations[f[1]] for f in friends]
    meet_durations = [f[4] for f in friends]
    meet_windows = [(f[2], f[3]) for f in friends]

    # Basic meeting constraints
    for i in range(len(friends)):
        s.add(meet_starts[i] >= meet_windows[i][0])
        s.add(meet_ends[i] <= meet_windows[i][1])
        s.add(meet_ends[i] - meet_starts[i] >= meet_durations[i])
        s.add(meet_starts[i] < meet_ends[i])

    # Create variables to track meeting sequence
    # We'll use a list to represent the order of meetings
    sequence = [Int(f'seq_{i}') for i in range(len(friends))]
    s.add(Distinct(sequence))
    for i in range(len(friends)):
        s.add(sequence[i] >= 0)
        s.add(sequence[i] < len(friends))

    # Travel time constraints between consecutive meetings
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                s.add(Implies(
                    sequence[i] + 1 == sequence[j],
                    meet_starts[j] >= meet_ends[i] + travel_times[meet_locs[i]][meet_locs[j]]
                ))

    # First meeting must be after travel from starting location
    for i in range(len(friends)):
        s.add(Implies(
            sequence[i] == 0,
            meet_starts[i] >= current_time + travel_times[current_loc][meet_locs[i]]
        ))

    # Try to maximize the number of meetings
    # We'll add soft constraints to prioritize longer meetings
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            if friends[i][4] > friends[j][4]:
                s.add(sequence[i] <= sequence[j])

    # Check for solution
    result = s.check()
    if result == sat:
        m = s.model()
        
        # Get meeting order
        meeting_order = sorted(
            [(i, m.evaluate(sequence[i]).as_long()) for i in range(len(friends))],
            key=lambda x: x[1]
        )
        
        # Verify all constraints are satisfied
        valid_schedule = True
        prev_end = current_time
        prev_loc = current_loc
        
        for idx, pos in meeting_order:
            start = m.evaluate(meet_starts[idx]).as_long()
            end = m.evaluate(meet_ends[idx]).as_long()
            loc = meet_locs[idx]
            
            # Check travel time from previous location
            if pos > 0:
                travel = travel_times[prev_loc][loc]
                if start < prev_end + travel:
                    valid_schedule = False
                    break
            
            prev_end = end
            prev_loc = loc
        
        if valid_schedule:
            # Build and print schedule
            print("SOLUTION:")
            for idx, pos in meeting_order:
                name = friends[idx][0]
                loc_name = friends[idx][1]
                start = m.evaluate(meet_starts[idx]).as_long()
                end = m.evaluate(meet_ends[idx]).as_long()
                print(f"Meet {name} at {loc_name} from {start//60:02d}:{start%60:02d} to {end//60:02d}:{end%60:02d}")
        else:
            print("No valid schedule found (constraints violated)")
    elif result == unsat:
        print("No feasible schedule exists that meets all constraints")
    else:
        print("Solver could not determine a solution (unknown)")

solve_scheduling()