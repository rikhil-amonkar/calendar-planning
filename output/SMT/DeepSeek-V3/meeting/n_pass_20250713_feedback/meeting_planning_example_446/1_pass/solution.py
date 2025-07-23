from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the districts and their indices for easy reference
    districts = {
        'Richmond': 0,
        'Marina': 1,
        'Chinatown': 2,
        'Financial': 3,
        'Bayview': 4,
        'UnionSquare': 5
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 9, 20, 22, 26, 21],    # Richmond to others
        [11, 0, 16, 17, 27, 16],   # Marina to others
        [20, 12, 0, 5, 22, 7],      # Chinatown to others
        [21, 15, 5, 0, 19, 9],      # Financial to others
        [25, 25, 18, 19, 0, 17],    # Bayview to others
        [20, 18, 7, 9, 15, 0]       # UnionSquare to others
    ]

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    # Friend data: name, district, start, end, min_duration
    friends = [
        ('Kimberly', districts['Marina'], time_to_minutes(13, 15), time_to_minutes(16, 45), 15),
        ('Robert', districts['Chinatown'], time_to_minutes(12, 15), time_to_minutes(20, 15), 15),
        ('Rebecca', districts['Financial'], time_to_minutes(13, 15), time_to_minutes(16, 45), 75),
        ('Margaret', districts['Bayview'], time_to_minutes(9, 30), time_to_minutes(13, 30), 30),
        ('Kenneth', districts['UnionSquare'], time_to_minutes(19, 30), time_to_minutes(21, 15), 75)
    ]

    # Variables for each friend: start and end times of meeting
    meeting_starts = [Int(f'start_{name}') for name, _, _, _, _ in friends]
    meeting_ends = [Int(f'end_{name}') for name, _, _, _, _ in friends]
    meet_friend = [Bool(f'meet_{name}') for name, _, _, _, _ in friends]  # Whether we meet the friend

    # Initial location: Richmond at time 0 (9:00 AM)
    current_location = districts['Richmond']
    current_time = 0

    # Constraints for each friend
    for i, (name, district, start, end, min_duration) in enumerate(friends):
        # If we meet the friend, the meeting must be within their availability
        s.add(Implies(meet_friend[i], And(
            meeting_starts[i] >= start,
            meeting_ends[i] <= end,
            meeting_ends[i] - meeting_starts[i] >= min_duration
        )))

        # If we meet the friend, the travel time must be accounted for
        if i > 0:
            # Travel from previous location to this friend's location
            s.add(Implies(And(meet_friend[i-1], meet_friend[i]),
                  meeting_starts[i] >= meeting_ends[i-1] + travel_times[friends[i-1][1]][district]))

    # First meeting: must account for travel from Richmond to the first friend's location
    for i in range(len(friends)):
        s.add(Implies(meet_friend[i], meeting_starts[i] >= travel_times[current_location][friends[i][1]]))

    # Last meeting: must end before Kenneth's end time (21:15 PM is 735 minutes, 735 - 540 = 195)
    s.add(Implies(meet_friend[-1], meeting_ends[-1] <= time_to_minutes(21, 15)))

    # Maximize the number of friends met
    s.maximize(Sum([If(meet_friend[i], 1, 0) for i in range(len(friends))]))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print("Optimal schedule:")
        total_met = 0
        for i, (name, district, _, _, _) in enumerate(friends):
            if m.evaluate(meet_friend[i]):
                start = m.evaluate(meeting_starts[i])
                end = m.evaluate(meeting_ends[i])
                print(f"Meet {name} at {district}: from {start + 540} minutes ({(start + 540) // 60}:{(start + 540) % 60:02d}) to {end + 540} minutes ({(end + 540) // 60}:{(end + 540) % 60:02d})")
                total_met += 1
        print(f"Total friends met: {total_met}")
    else:
        print("No solution found.")

solve_scheduling()