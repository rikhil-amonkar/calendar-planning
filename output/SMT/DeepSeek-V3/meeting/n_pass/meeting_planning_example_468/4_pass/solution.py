from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Friends and their availability
    friends = {
        "Rebecca": {"location": "Bayview", "start": 9*60, "end": 12*60 + 45, "duration": 90},
        "Amanda": {"location": "Pacific Heights", "start": 18*60 + 30, "end": 21*60 + 45, "duration": 90},
        "James": {"location": "Alamo Square", "start": 9*60 + 45, "end": 21*60 + 15, "duration": 90},
        "Sarah": {"location": "Fisherman's Wharf", "start": 8*60, "end": 21*60 + 30, "duration": 90},
        "Melissa": {"location": "Golden Gate Park", "start": 9*60, "end": 18*60 + 45, "duration": 90}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "The Castro": {
            "Bayview": 19,
            "Pacific Heights": 16,
            "Alamo Square": 8,
            "Fisherman's Wharf": 24,
            "Golden Gate Park": 11
        },
        "Bayview": {
            "The Castro": 20,
            "Pacific Heights": 23,
            "Alamo Square": 16,
            "Fisherman's Wharf": 25,
            "Golden Gate Park": 22
        },
        "Pacific Heights": {
            "The Castro": 16,
            "Bayview": 22,
            "Alamo Square": 10,
            "Fisherman's Wharf": 13,
            "Golden Gate Park": 15
        },
        "Alamo Square": {
            "The Castro": 8,
            "Bayview": 16,
            "Pacific Heights": 10,
            "Fisherman's Wharf": 19,
            "Golden Gate Park": 9
        },
        "Fisherman's Wharf": {
            "The Castro": 26,
            "Bayview": 26,
            "Pacific Heights": 12,
            "Alamo Square": 20,
            "Golden Gate Park": 25
        },
        "Golden Gate Park": {
            "The Castro": 13,
            "Bayview": 23,
            "Pacific Heights": 16,
            "Alamo Square": 10,
            "Fisherman's Wharf": 24
        }
    }

    # Decision variables: whether to meet each friend
    meet_vars = {name: Bool(f"meet_{name}") for name in friends}

    # Meeting start and end times (in minutes since midnight)
    start_times = {name: Int(f"start_{name}") for name in friends}
    end_times = {name: Int(f"end_{name}") for name in friends}

    # Current location starts at The Castro at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes

    # Constraints for each friend
    for name in friends:
        info = friends[name]
        s.add(Implies(meet_vars[name], start_times[name] >= info["start"]))
        s.add(Implies(meet_vars[name], end_times[name] <= info["end"]))
        s.add(Implies(meet_vars[name], end_times[name] == start_times[name] + info["duration"]))

    # Define order variables to sequence the meetings
    # We'll create a list of all possible meeting orders and let Z3 choose
    all_friends = list(friends.keys())
    num_friends = len(all_friends)
    
    # Create variables to represent the order
    order = [Int(f"order_{i}") for i in range(num_friends)]
    # Each order variable should be between 0 and num_friends-1
    for o in order:
        s.add(o >= 0, o < num_friends)
    # All order variables should be distinct
    s.add(Distinct(order))
    
    # Create variables to track previous location and time
    prev_locs = [String(f"prev_loc_{i}") for i in range(num_friends)]
    prev_times = [Int(f"prev_time_{i}") for i in range(num_friends)]
    
    # Initialize first step
    s.add(prev_locs[0] == "The Castro")
    s.add(prev_times[0] == current_time)
    
    # Add constraints for each step in the order
    for i in range(num_friends):
        # Get the friend at this position
        friend = all_friends[order[i]]
        # Add travel time constraint
        s.add(Implies(meet_vars[friend], 
                      start_times[friend] >= prev_times[i] + travel_times[prev_locs[i]][friends[friend]["location"]]))
        # Update previous location and time
        if i < num_friends - 1:
            s.add(prev_locs[i+1] == If(meet_vars[friend], friends[friend]["location"], prev_locs[i]))
            s.add(prev_times[i+1] == If(meet_vars[friend], end_times[friend], prev_times[i]))

    # Also, ensure that if we don't meet someone, their start and end times are irrelevant
    for name in friends:
        s.add(Implies(Not(meet_vars[name]), start_times[name] == 0))
        s.add(Implies(Not(meet_vars[name]), end_times[name] == 0))

    # Maximize the number of friends met
    total_met = Sum([If(meet_vars[name], 1, 0) for name in friends])
    s.maximize(total_met)

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        itinerary = []
        met_friends = []
        for name in friends:
            if model.evaluate(meet_vars[name]):
                start = model.evaluate(start_times[name]).as_long()
                end = model.evaluate(end_times[name]).as_long()
                start_h = start // 60
                start_m = start % 60
                end_h = end // 60
                end_m = end % 60
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start_h:02d}:{start_m:02d}",
                    "end_time": f"{end_h:02d}:{end_m:02d}"
                })
                met_friends.append(name)
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x['start_time'].split(':')[0]), int(x['start_time'].split(':')[1])))
        print(f"Met friends: {met_friends}")
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))