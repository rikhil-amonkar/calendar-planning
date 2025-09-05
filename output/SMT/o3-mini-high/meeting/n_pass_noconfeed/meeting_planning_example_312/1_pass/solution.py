import json
from z3 import *

def main():
    # Create an optimizer instance
    opt = Optimize()

    # Define friends and their meeting details
    friends = ["Sarah", "Richard", "Elizabeth", "Michelle"]
    locations = {
        "Sarah": "Sunset District",
        "Richard": "Haight-Ashbury",
        "Elizabeth": "Mission District",
        "Michelle": "Golden Gate Park"
    }
    durations = {
        "Sarah": 30,      # in minutes
        "Richard": 90,
        "Elizabeth": 120,
        "Michelle": 90
    }
    # Availability times are expressed in minutes after 9:00AM.
    avail_start = {
        "Sarah": 105,     # 10:45AM
        "Richard": 165,   # 11:45AM
        "Elizabeth": 120, # 11:00AM
        "Michelle": 555   # 18:15 (6:15PM)
    }
    avail_end = {
        "Sarah": 600,     # 19:00 (7:00PM)
        "Richard": 405,   # 15:45 (3:45PM)
        "Elizabeth": 495, # 17:15 (5:15PM)
        "Michelle": 705   # 20:45 (8:45PM)
    }
    # Travel time (in minutes) from the starting location (Richmond District) to each meeting location.
    initial_travel = {
        "Sarah": 11,      # Richmond -> Sunset District
        "Richard": 10,    # Richmond -> Haight-Ashbury
        "Elizabeth": 20,  # Richmond -> Mission District
        "Michelle": 9     # Richmond -> Golden Gate Park
    }
    # Travel time (in minutes) between the meeting locations.
    # Keys are tuples (from_location, to_location)
    travel = {
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Mission District"): 24,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Golden Gate Park"): 17,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Mission District"): 17
    }

    n = len(friends)
    # Decision variables:
    # attend[i]: whether to meet friend i.
    attend = [Bool(f"attend_{i}") for i in range(n)]
    # start_vars[i]: meeting start time (in minutes after 9:00AM) for friend i.
    start_vars = [Int(f"start_{i}") for i in range(n)]
    # order_vars[i]: the order in which friend i is met.
    # If a friend is not met, we set its order to -1.
    order_vars = [Int(f"order_{i}") for i in range(n)]
    
    # Add constraints for each friend meeting if scheduled.
    for i, friend in enumerate(friends):
        # When meeting is scheduled, the meeting must occur within that friend’s availability.
        opt.add(Implies(attend[i], start_vars[i] >= avail_start[friend]))
        opt.add(Implies(attend[i], start_vars[i] + durations[friend] <= avail_end[friend]))
        # If meeting is scheduled, force its order to be between 0 and n-1.
        opt.add(Implies(attend[i], And(order_vars[i] >= 0, order_vars[i] < n)))
        # If not scheduled, set order to -1 (an out-of-range value).
        opt.add(Implies(Not(attend[i]), order_vars[i] == -1))
    
    # Enforce that the order of attended meetings is distinct.
    for i in range(n):
        for j in range(i + 1, n):
            opt.add(Implies(And(attend[i], attend[j]), order_vars[i] != order_vars[j]))
    
    # For any two meetings that are scheduled, if friend i is met before friend j,
    # then friend j's meeting must start after friend i’s meeting ends plus travel time.
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            loc_i = locations[friends[i]]
            loc_j = locations[friends[j]]
            if (loc_i, loc_j) in travel:
                travel_time = travel[(loc_i, loc_j)]
                opt.add(
                    Implies(
                        And(attend[i], attend[j], order_vars[i] < order_vars[j]),
                        start_vars[j] >= start_vars[i] + durations[friends[i]] + travel_time
                    )
                )
    # For the first meeting in the sequence (order == 0), ensure that the meeting start time
    # accounts for travel from Richmond District.
    for i, friend in enumerate(friends):
        opt.add(Implies(And(attend[i], order_vars[i] == 0), start_vars[i] >= initial_travel[friend]))

    # Define the objective: maximize the number of meetings (i.e. friends met).
    total_meetings = Sum([If(attend[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)
    
    # Solve the constraints.
    if opt.check() == sat:
        model = opt.model()
        # Build a list of scheduled meetings (only those with attend==True)
        scheduled = []
        for i in range(n):
            if model.evaluate(attend[i]):
                order_val = model.evaluate(order_vars[i]).as_long()
                start_val = model.evaluate(start_vars[i]).as_long()
                scheduled.append((order_val, i, start_val))
        # Sort the meetings by their scheduled order
        scheduled.sort(key=lambda x: x[0])
        itinerary = []
        for order_val, i, start_val in scheduled:
            friend = friends[i]
            loc = locations[friend]
            # Meeting end time is start time plus its duration.
            end_val = start_val + durations[friend]
            # Convert meeting times (minutes after 9:00) to actual clock times.
            # 9:00AM corresponds to 9*60 = 540 minutes after midnight.
            real_start = 540 + start_val
            real_end = 540 + end_val
            start_hours = real_start // 60
            start_minutes = real_start % 60
            end_hours = real_end // 60
            end_minutes = real_end % 60
            start_str = f"{start_hours}:{start_minutes:02d}"
            end_str = f"{end_hours}:{end_minutes:02d}"
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": friend,
                "start_time": start_str,
                "end_time": end_str
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # If no schedule is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()