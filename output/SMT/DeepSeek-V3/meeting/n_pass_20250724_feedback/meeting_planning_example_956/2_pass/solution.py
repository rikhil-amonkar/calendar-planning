from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

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
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Golden Gate Park"): 23,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Golden Gate Park"): 22,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Golden Gate Park"): 18,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Golden Gate Park"): 17,
        ("Pacific Heights", "Golden Gate Park"): 16
    }

    # Define a variable to represent the order of meetings
    order = [Int(f"order_{friend['name']}") for friend in friends]
    s.add(Distinct(order))
    for i in range(len(friends)):
        s.add(order[i] >= 0)
        s.add(order[i] < len(friends))

    # Add constraints for travel times between consecutive meetings
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                # If friend i is before friend j in the order
                s.add(Implies(order[i] < order[j],
                           friends[j]["var_start"] >= friends[i]["var_end"] + 
                           travel_times.get((friends[i]["location"], friends[j]["location"]), 0)))

    # Maximize the number of friends met
    s.maximize(Sum([If(friends[i]["var_end"] > 0, 1, 0) for i in range(len(friends))]))

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