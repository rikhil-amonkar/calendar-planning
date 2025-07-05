from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define the locations and their indices
    locations = {
        'Golden_Gate_Park': 0,
        'Haight_Ashbury': 1,
        'Sunset_District': 2,
        'Marina_District': 3,
        'Financial_District': 4,
        'Union_Square': 5
    }

    # Travel times matrix (in minutes)
    travel_times = [
        [0, 7, 10, 16, 26, 22],    # Golden Gate Park
        [7, 0, 15, 17, 21, 17],     # Haight-Ashbury
        [11, 15, 0, 21, 30, 30],    # Sunset District
        [18, 16, 19, 0, 17, 16],    # Marina District
        [23, 19, 31, 15, 0, 9],     # Financial District
        [22, 18, 26, 18, 9, 0]      # Union Square
    ]

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    # Friend constraints
    friends = [
        {'name': 'Sarah', 'location': 'Haight_Ashbury', 'start': time_to_minutes(17, 0), 'end': time_to_minutes(21, 30), 'duration': 105},
        {'name': 'Patricia', 'location': 'Sunset_District', 'start': time_to_minutes(17, 0), 'end': time_to_minutes(19, 45), 'duration': 45},
        {'name': 'Matthew', 'location': 'Marina_District', 'start': time_to_minutes(9, 15), 'end': time_to_minutes(12, 0), 'duration': 15},
        {'name': 'Joseph', 'location': 'Financial_District', 'start': time_to_minutes(14, 15), 'end': time_to_minutes(18, 45), 'duration': 30},
        {'name': 'Robert', 'location': 'Union_Square', 'start': time_to_minutes(10, 15), 'end': time_to_minutes(21, 45), 'duration': 15}
    ]

    # Variables for arrival and departure times at each location
    arrival = [Int(f'arrival_{loc}') for loc in locations.keys()]
    departure = [Int(f'departure_{loc}') for loc in locations.keys()]

    # Initial constraints: start at Golden Gate Park at 9:00 AM (0 minutes)
    s.add(arrival[locations['Golden_Gate_Park']] == 0)
    s.add(departure[locations['Golden_Gate_Park']] >= 0)

    # Constraints for each friend
    met_friends = []
    for friend in friends:
        loc_idx = locations[friend['location']]
        meet_start = Int(f'meet_start_{friend["name"]}')
        meet_end = Int(f'meet_end_{friend["name"]}')

        # Meeting must be within friend's availability
        s.add(meet_start >= friend['start'])
        s.add(meet_end <= friend['end'])
        s.add(meet_end - meet_start >= friend['duration'])

        # Arrival and departure at the location must include the meeting
        s.add(arrival[loc_idx] <= meet_start)
        s.add(departure[loc_idx] >= meet_end)

    # Constraints for travel between locations
    for i in range(len(locations)):
        for j in range(len(locations)):
            if i != j:
                # If you go from i to j, departure[i] + travel_time <= arrival[j]
                s.add(Implies(
                    And(departure[i] >= 0, arrival[j] >= 0),
                    departure[i] + travel_times[i][j] <= arrival[j]
                ))

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        print("Optimal schedule found. All friends met:")
        for friend in friends:
            print(f"- {friend['name']} at {friend['location']}")

        # Print the schedule
        print("\nSchedule:")
        for loc in locations:
            arr = model.eval(arrival[locations[loc]])
            dep = model.eval(departure[locations[loc]])
            if arr.as_long() >= 0 and dep.as_long() >= 0:
                print(f"{loc}: Arrive at {(arr.as_long() + 540) // 60}:{(arr.as_long() + 540) % 60:02d}, Depart at {(dep.as_long() + 540) // 60}:{(dep.as_long() + 540) % 60:02d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()