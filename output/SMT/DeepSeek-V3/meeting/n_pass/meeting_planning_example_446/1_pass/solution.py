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

    # Travel times matrix (minutes)
    travel_times = [
        [0, 9, 20, 22, 26, 21],    # Richmond to others
        [11, 0, 16, 17, 27, 16],    # Marina to others
        [20, 12, 0, 5, 22, 7],      # Chinatown to others
        [21, 15, 5, 0, 19, 9],       # Financial to others
        [25, 25, 18, 19, 0, 17],    # Bayview to others
        [20, 18, 7, 9, 15, 0]        # UnionSquare to others
    ]

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    # Friends' availability and constraints
    friends = [
        {'name': 'Kimberly', 'district': 'Marina', 'start': time_to_minutes(13, 15), 'end': time_to_minutes(16, 45), 'duration': 15},
        {'name': 'Robert', 'district': 'Chinatown', 'start': time_to_minutes(12, 15), 'end': time_to_minutes(20, 15), 'duration': 15},
        {'name': 'Rebecca', 'district': 'Financial', 'start': time_to_minutes(13, 15), 'end': time_to_minutes(16, 45), 'duration': 75},
        {'name': 'Margaret', 'district': 'Bayview', 'start': time_to_minutes(9, 30), 'end': time_to_minutes(13, 30), 'duration': 30},
        {'name': 'Kenneth', 'district': 'UnionSquare', 'start': time_to_minutes(19, 30), 'end': time_to_minutes(21, 15), 'duration': 75}
    ]

    # Variables for each friend: arrival time, departure time, and whether they are met
    meet_vars = []
    for friend in friends:
        arrival = Int(f"arrival_{friend['name']}")
        departure = Int(f"departure_{friend['name']}")
        met = Bool(f"met_{friend['name']}")
        meet_vars.append((friend, arrival, departure, met))

    # Initial constraints: start at Richmond at time 0 (9:00 AM)
    s.add(meet_vars[0][1] == 0)  # First arrival is at Richmond at time 0

    # Constraints for each friend
    for (friend, arrival, departure, met) in meet_vars:
        district_idx = districts[friend['district']]
        # If met, arrival and departure must be within friend's availability
        s.add(Implies(met, arrival >= friend['start']))
        s.add(Implies(met, departure <= friend['end']))
        s.add(Implies(met, departure - arrival >= friend['duration']))
        # If not met, arrival and departure are unconstrained (but we'll optimize to meet as many as possible)

    # Travel time constraints between consecutive meetings
    for i in range(len(meet_vars) - 1):
        (friend1, _, departure1, met1) = meet_vars[i]
        (friend2, arrival2, _, met2) = meet_vars[i + 1]
        district1 = districts[friend1['district']]
        district2 = districts[friend2['district']]
        travel_time = travel_times[district1][district2]
        # If both are met, travel time must be accounted for
        s.add(Implies(And(met1, met2), arrival2 >= departure1 + travel_time))

    # Objective: maximize the number of friends met
    num_met = sum([If(met, 1, 0) for (_, _, _, met) in meet_vars])
    s.maximize(num_met)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        total_met = 0
        schedule = []
        for (friend, arrival, departure, met) in meet_vars:
            if m.evaluate(met):
                total_met += 1
                arr = m.evaluate(arrival).as_long() + 540
                dep = m.evaluate(departure).as_long() + 540
                arr_time = f"{arr // 60}:{arr % 60:02d}"
                dep_time = f"{dep // 60}:{dep % 60:02d}"
                schedule.append((friend['name'], friend['district'], arr_time, dep_time))
        print(f"Total friends met: {total_met}")
        for entry in schedule:
            print(f"Meet {entry[0]} at {entry[1]} from {entry[2]} to {entry[3]}")
    else:
        print("No feasible schedule found.")

solve_scheduling()