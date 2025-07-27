from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define friends and their constraints
    friends = [
        {"name": "William", "location": "Alamo Square", "start": 15*60 + 15, "end": 17*60 + 15, "min_duration": 60},
        {"name": "Joshua", "location": "Richmond District", "start": 7*60, "end": 20*60, "min_duration": 15},
        {"name": "Joseph", "location": "Financial District", "start": 11*60 + 15, "end": 13*60 + 30, "min_duration": 15},
        {"name": "David", "location": "Union Square", "start": 16*60 + 45, "end": 19*60 + 15, "min_duration": 45},
        {"name": "Brian", "location": "Fisherman's Wharf", "start": 13*60 + 45, "end": 20*60 + 45, "min_duration": 105},
        {"name": "Karen", "location": "Marina District", "start": 11*60 + 30, "end": 18*60 + 30, "min_duration": 15},
        {"name": "Anthony", "location": "Haight-Ashbury", "start": 7*60 + 15, "end": 10*60 + 30, "min_duration": 30},
        {"name": "Matthew", "location": "Mission District", "start": 17*60 + 15, "end": 19*60 + 15, "min_duration": 120},
        {"name": "Helen", "location": "Pacific Heights", "start": 8*60, "end": 12*60, "min_duration": 75},
        {"name": "Jeffrey", "location": "Golden Gate Park", "start": 19*60, "end": 21*60 + 30, "min_duration": 60}
    ]

    # Create variables for each friend's meeting start and end times (in minutes since 9:00 AM, which is 0)
    for friend in friends:
        friend["var_start"] = Int(f"start_{friend['name']}")
        friend["var_end"] = Int(f"end_{friend['name']}")
        # Constrain meeting to be within friend's availability
        s.add(friend["var_start"] >= friend["start"] - 9*60)
        s.add(friend["var_end"] <= friend["end"] - 9*60)
        s.add(friend["var_end"] - friend["var_start"] >= friend["min_duration"])
        s.add(friend["var_start"] >= 0)  # Cannot start before 9:00 AM

    # Define travel times between locations (from Castro initially)
    travel_times = {
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Golden Gate Park"): 11,
    }

    # Add travel times between meetings
    # We need to sequence meetings such that travel time is accounted for
    # For simplicity, assume meetings are in order and add constraints accordingly
    # This is a simplified approach; a more sophisticated method would involve ordering variables
    # Here, we'll prioritize meeting friends with tighter time windows first

    # For now, let's try to meet all friends in an order that fits
    # We'll manually attempt a feasible order based on time windows and travel times

    # Let's try meeting Anthony first (since his window is earliest)
    # Then Helen, Joseph, Karen, Brian, William, David, Matthew, Jeffrey, Joshua

    # Define the order of meetings
    meeting_order = [
        "Anthony",
        "Helen",
        "Joseph",
        "Karen",
        "Brian",
        "William",
        "David",
        "Matthew",
        "Jeffrey",
        "Joshua"
    ]

    # Get friend objects in order
    ordered_friends = [next(f for f in friends if f["name"] == name) for name in meeting_order]

    # Add constraints for travel times between consecutive meetings
    prev_end = 0  # Start at 9:00 AM (0 minutes after)
    prev_location = "The Castro"
    for i in range(len(ordered_friends)):
        current_friend = ordered_friends[i]
        # Current meeting must start after previous end + travel time
        travel_time = travel_times.get((prev_location, current_friend["location"]), 0)
        s.add(current_friend["var_start"] >= prev_end + travel_time)
        prev_end = current_friend["var_end"]
        prev_location = current_friend["location"]

    # Check if all constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for friend in friends:
            start = m.evaluate(friend["var_start"]).as_long()
            end = m.evaluate(friend["var_end"]).as_long()
            start_time = f"{9 + start // 60:02d}:{start % 60:02d}"
            end_time = f"{9 + end // 60:02d}:{end % 60:02d}"
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": start_time,
                "end_time": end_time
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
result = solve_scheduling()
print(result)