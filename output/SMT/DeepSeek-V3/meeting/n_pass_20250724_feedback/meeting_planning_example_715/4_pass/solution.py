from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define friends and their details
    friends = {
        "Amanda": {"location": "Marina District", "start": (14, 45), "end": (19, 30), "min_duration": 105},
        "Melissa": {"location": "The Castro", "start": (9, 30), "end": (17, 0), "min_duration": 30},
        "Jeffrey": {"location": "Fisherman's Wharf", "start": (12, 45), "end": (18, 45), "min_duration": 120},
        "Matthew": {"location": "Bayview", "start": (10, 15), "end": (13, 15), "min_duration": 30},
        "Nancy": {"location": "Pacific Heights", "start": (17, 0), "end": (21, 30), "min_duration": 105},
        "Karen": {"location": "Mission District", "start": (17, 30), "end": (20, 30), "min_duration": 105},
        "Robert": {"location": "Alamo Square", "start": (11, 15), "end": (17, 30), "min_duration": 120},
        "Joseph": {"location": "Golden Gate Park", "start": (8, 30), "end": (21, 15), "min_duration": 105}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        "Presidio": {
            "Marina District": 11,
            "The Castro": 21,
            "Fisherman's Wharf": 19,
            "Bayview": 31,
            "Pacific Heights": 11,
            "Mission District": 26,
            "Alamo Square": 19,
            "Golden Gate Park": 12
        },
        "Marina District": {
            "Presidio": 10,
            "The Castro": 22,
            "Fisherman's Wharf": 10,
            "Bayview": 27,
            "Pacific Heights": 7,
            "Mission District": 20,
            "Alamo Square": 15,
            "Golden Gate Park": 18
        },
        "The Castro": {
            "Presidio": 20,
            "Marina District": 21,
            "Fisherman's Wharf": 24,
            "Bayview": 19,
            "Pacific Heights": 16,
            "Mission District": 7,
            "Alamo Square": 8,
            "Golden Gate Park": 11
        },
        "Fisherman's Wharf": {
            "Presidio": 17,
            "Marina District": 9,
            "The Castro": 27,
            "Bayview": 26,
            "Pacific Heights": 12,
            "Mission District": 22,
            "Alamo Square": 21,
            "Golden Gate Park": 25
        },
        "Bayview": {
            "Presidio": 32,
            "Marina District": 27,
            "The Castro": 19,
            "Fisherman's Wharf": 25,
            "Pacific Heights": 23,
            "Mission District": 13,
            "Alamo Square": 16,
            "Golden Gate Park": 22
        },
        "Pacific Heights": {
            "Presidio": 11,
            "Marina District": 6,
            "The Castro": 16,
            "Fisherman's Wharf": 13,
            "Bayview": 22,
            "Mission District": 15,
            "Alamo Square": 10,
            "Golden Gate Park": 15
        },
        "Mission District": {
            "Presidio": 25,
            "Marina District": 19,
            "The Castro": 7,
            "Fisherman's Wharf": 22,
            "Bayview": 14,
            "Pacific Heights": 16,
            "Alamo Square": 11,
            "Golden Gate Park": 17
        },
        "Alamo Square": {
            "Presidio": 17,
            "Marina District": 15,
            "The Castro": 8,
            "Fisherman's Wharf": 19,
            "Bayview": 16,
            "Pacific Heights": 10,
            "Mission District": 10,
            "Golden Gate Park": 9
        },
        "Golden Gate Park": {
            "Presidio": 11,
            "Marina District": 16,
            "The Castro": 13,
            "Fisherman's Wharf": 24,
            "Bayview": 23,
            "Pacific Heights": 16,
            "Mission District": 17,
            "Alamo Square": 9
        }
    }

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(m):
        total = m + 540
        h = total // 60
        m = total % 60
        return f"{h:02d}:{m:02d}"

    # Create Z3 variables for each meeting's start and end times
    meet_vars = {}
    for name in friends:
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        meet_vars[name] = {"start": start_var, "end": end_var}

    # Add constraints for each friend
    for name in friends:
        friend = friends[name]
        start_min = time_to_minutes(*friend["start"])
        end_min = time_to_minutes(*friend["end"])
        min_duration = friend["min_duration"]

        # Meeting must be within friend's availability
        s.add(meet_vars[name]["start"] >= start_min)
        s.add(meet_vars[name]["end"] <= end_min)
        s.add(meet_vars[name]["end"] - meet_vars[name]["start"] >= min_duration)

    # Define the order of meetings using a list of Int variables
    num_friends = len(friends)
    friend_names = list(friends.keys())
    order = [Int(f"order_{i}") for i in range(num_friends)]
    
    # Each order variable must be between 0 and num_friends - 1
    for o in order:
        s.add(o >= 0)
        s.add(o < num_friends)
    
    # All order variables must be distinct
    s.add(Distinct(order))

    # Create a mapping from friend names to their index
    name_to_index = {name: i for i, name in enumerate(friend_names)}

    # Ensure the order respects travel times
    for i in range(num_friends - 1):
        current_order = order[i]
        next_order = order[i + 1]
        
        # Create constraints for each possible pair of friends
        for j in range(num_friends):
            for k in range(num_friends):
                if j != k:
                    current_friend = friend_names[j]
                    next_friend = friend_names[k]
                    current_loc = friends[current_friend]["location"]
                    next_loc = friends[next_friend]["location"]
                    travel_time = travel_times[current_loc][next_loc]
                    
                    # If current_order is j and next_order is k, then add the travel time constraint
                    s.add(Implies(And(current_order == j, next_order == k),
                           meet_vars[next_friend]["start"] >= meet_vars[current_friend]["end"] + travel_time))

    # The first meeting must start after traveling from Presidio
    for j in range(num_friends):
        first_friend = friend_names[j]
        first_loc = friends[first_friend]["location"]
        travel_time = travel_times["Presidio"][first_loc]
        s.add(Implies(order[0] == j, meet_vars[first_friend]["start"] >= travel_time))

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        # Extract the order from the model
        ordered_indices = [model[o].as_long() for o in order]
        ordered_friends = [friend_names[i] for i in ordered_indices]
        # Build the itinerary in the correct order
        itinerary = []
        for name in ordered_friends:
            start = model[meet_vars[name]["start"]].as_long()
            end = model[meet_vars[name]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the problem and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))