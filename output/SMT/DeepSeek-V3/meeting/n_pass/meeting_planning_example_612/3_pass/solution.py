from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Location indices
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

    # Friends data: name, location, start, end, min_duration
    friends = [
        ('Emily', 'Russian Hill', 735, 855, 105),    # 12:15-14:15
        ('Mark', 'Presidio', 885, 1170, 60),        # 14:45-19:30
        ('Deborah', 'Chinatown', 450, 930, 45),     # 7:30-15:30
        ('Margaret', 'Sunset District', 1290, 1350, 60),  # 21:30-22:30
        ('George', 'The Castro', 450, 855, 60),     # 7:30-14:15
        ('Andrew', 'Embarcadero', 1215, 1320, 75),  # 20:15-22:00
        ('Steven', 'Golden Gate Park', 675, 1275, 105)   # 11:15-21:15
    ]

    # Start at Alamo Square at 9:00 (540 minutes)
    current_time = 540
    current_loc = locations['Alamo Square']

    # Create variables for each meeting
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

    # Meeting ordering constraints
    # We'll create a permutation variable to determine meeting order
    order = [Int(f'order_{i}') for i in range(len(friends))]
    s.add(Distinct(order))
    for i in range(len(friends)):
        s.add(order[i] >= 0)
        s.add(order[i] < len(friends))

    # Travel time constraints
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                # If meeting i comes before meeting j in order
                s.add(Implies(
                    order[i] < order[j],
                    meet_starts[j] >= meet_ends[i] + travel_times[meet_locs[i]][meet_locs[j]]
                ))

    # First meeting must be after travel from starting location
    for i in range(len(friends)):
        s.add(Implies(
            order[i] == 0,
            meet_starts[i] >= current_time + travel_times[current_loc][meet_locs[i]]
        ))

    # Check if solution exists
    if s.check() == sat:
        m = s.model()
        
        # Get meeting order
        meeting_order = sorted(
            [(i, m.evaluate(order[i]).as_long()) for i in range(len(friends))],
            key=lambda x: x[1]
        )
        
        # Build schedule
        schedule = []
        for idx, pos in meeting_order:
            name = friends[idx][0]
            loc = friends[idx][1]
            start = m.evaluate(meet_starts[idx]).as_long()
            end = m.evaluate(meet_ends[idx]).as_long()
            schedule.append((name, loc, start, end))
        
        # Print schedule
        print("SOLUTION:")
        for name, loc, start, end in schedule:
            print(f"Meet {name} at {loc} from {start//60:02d}:{start%60:02d} to {end//60:02d}:{end%60:02d}")
    else:
        print("No feasible schedule found")

solve_scheduling()