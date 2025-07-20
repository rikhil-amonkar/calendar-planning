from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Friends and their details
    friends = [
        {"name": "Kevin", "location": "Pacific Heights", "start": "7:15", "end": "8:45", "duration": 90},
        {"name": "Michelle", "location": "Golden Gate Park", "start": "20:00", "end": "21:00", "duration": 15},
        {"name": "Emily", "location": "Fisherman's Wharf", "start": "16:15", "end": "19:00", "duration": 30},
        {"name": "Mark", "location": "Marina District", "start": "18:15", "end": "19:45", "duration": 75},
        {"name": "Barbara", "location": "Alamo Square", "start": "17:00", "end": "19:00", "duration": 120},
        {"name": "Laura", "location": "Sunset District", "start": "19:00", "end": "21:15", "duration": 75},
        {"name": "Mary", "location": "Nob Hill", "start": "17:30", "end": "19:00", "duration": 45},
        {"name": "Helen", "location": "North Beach", "start": "11:00", "end": "12:15", "duration": 45}
    ]

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    # Prepare friend data with minutes
    for friend in friends:
        friend["start_min"] = time_to_minutes(friend["start"])
        friend["end_min"] = time_to_minutes(friend["end"])

    # Decision variables: whether to meet each friend
    meet_vars = {friend["name"]: Bool(f"meet_{friend['name']}") for friend in friends}

    # Start and end times for each friend (if met)
    start_vars = {friend["name"]: Int(f"start_{friend['name']}") for friend in friends}
    end_vars = {friend["name"]: Int(f"end_{friend['name']}") for friend in friends}

    # Constraints for each friend
    for friend in friends:
        name = friend["name"]
        opt.add(Implies(meet_vars[name], start_vars[name] >= friend["start_min"]))
        opt.add(Implies(meet_vars[name], end_vars[name] <= friend["end_min"]))
        opt.add(Implies(meet_vars[name], end_vars[name] == start_vars[name] + friend["duration"]))
        opt.add(Implies(Not(meet_vars[name]), start_vars[name] == -1))
        opt.add(Implies(Not(meet_vars[name]), end_vars[name] == -1))

    # Travel times dictionary (simplified for this example)
    travel_times = {
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "North Beach"): 18,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "North Beach"): 9,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "North Beach"): 23,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "North Beach"): 11,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "North Beach"): 15,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "North Beach"): 28,
        ("Nob Hill", "North Beach"): 8,
    }

    # Maximize the number of friends met
    opt.maximize(Sum([If(meet_vars[friend["name"]], 1, 0) for friend in friends]))

    # Check satisfiability
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for friend in friends:
            name = friend["name"]
            if m.evaluate(meet_vars[name]):
                start = m.evaluate(start_vars[name])
                end = m.evaluate(end_vars[name])
                start_min = start.as_long() + 540  # Convert back to minutes since midnight
                end_min = end.as_long() + 540
                start_time = f"{start_min // 60:02d}:{start_min % 60:02d}"
                end_time = f"{end_min // 60:02d}:{end_min % 60:02d}"
                itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the optimizer
result = solve_scheduling()
print(json.dumps(result, indent=2))