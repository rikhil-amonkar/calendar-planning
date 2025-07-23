from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 optimizer (not Solver)
    opt = Optimize()

    # Define friends and their details
    friends = {
        "Brian": {"location": "North Beach", "start": 13.0, "end": 19.0, "duration": 1.5},
        "Richard": {"location": "Fisherman's Wharf", "start": 11.0, "end": 12.75, "duration": 1.0},
        "Ashley": {"location": "Haight-Ashbury", "start": 15.0, "end": 20.5, "duration": 1.5},
        "Elizabeth": {"location": "Nob Hill", "start": 11.75, "end": 18.5, "duration": 1.25},
        "Jessica": {"location": "Golden Gate Park", "start": 20.0, "end": 21.75, "duration": 1.75},
        "Deborah": {"location": "Union Square", "start": 17.5, "end": 22.0, "duration": 1.0},
        "Kimberly": {"location": "Alamo Square", "start": 17.5, "end": 21.25, "duration": 0.75},
        "Matthew": {"location": "Presidio", "start": 8.25, "end": 9.0, "duration": 0.25},
        "Kenneth": {"location": "Chinatown", "start": 13.75, "end": 19.5, "duration": 1.75},
        "Anthony": {"location": "Pacific Heights", "start": 14.25, "end": 16.0, "duration": 0.5}
    }

    # Travel times dictionary
    travel_times = {
        ("Bayview", "North Beach"): 22/60,
        ("Bayview", "Fisherman's Wharf"): 25/60,
        ("Bayview", "Haight-Ashbury"): 19/60,
        ("Bayview", "Nob Hill"): 20/60,
        ("Bayview", "Golden Gate Park"): 22/60,
        ("Bayview", "Union Square"): 18/60,
        ("Bayview", "Alamo Square"): 16/60,
        ("Bayview", "Presidio"): 32/60,
        ("Bayview", "Chinatown"): 19/60,
        ("Bayview", "Pacific Heights"): 23/60,
        ("North Beach", "Fisherman's Wharf"): 5/60,
        ("North Beach", "Haight-Ashbury"): 18/60,
        ("North Beach", "Nob Hill"): 7/60,
        ("North Beach", "Golden Gate Park"): 22/60,
        ("North Beach", "Union Square"): 7/60,
        ("North Beach", "Alamo Square"): 16/60,
        ("North Beach", "Presidio"): 17/60,
        ("North Beach", "Chinatown"): 6/60,
        ("North Beach", "Pacific Heights"): 8/60,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22/60,
        ("Fisherman's Wharf", "Nob Hill"): 11/60,
        ("Fisherman's Wharf", "Golden Gate Park"): 25/60,
        ("Fisherman's Wharf", "Union Square"): 13/60,
        ("Fisherman's Wharf", "Alamo Square"): 21/60,
        ("Fisherman's Wharf", "Presidio"): 17/60,
        ("Fisherman's Wharf", "Chinatown"): 12/60,
        ("Fisherman's Wharf", "Pacific Heights"): 12/60,
        ("Haight-Ashbury", "Nob Hill"): 15/60,
        ("Haight-Ashbury", "Golden Gate Park"): 7/60,
        ("Haight-Ashbury", "Union Square"): 19/60,
        ("Haight-Ashbury", "Alamo Square"): 5/60,
        ("Haight-Ashbury", "Presidio"): 15/60,
        ("Haight-Ashbury", "Chinatown"): 19/60,
        ("Haight-Ashbury", "Pacific Heights"): 12/60,
        ("Nob Hill", "Golden Gate Park"): 17/60,
        ("Nob Hill", "Union Square"): 7/60,
        ("Nob Hill", "Alamo Square"): 11/60,
        ("Nob Hill", "Presidio"): 17/60,
        ("Nob Hill", "Chinatown"): 6/60,
        ("Nob Hill", "Pacific Heights"): 8/60,
        ("Golden Gate Park", "Union Square"): 22/60,
        ("Golden Gate Park", "Alamo Square"): 9/60,
        ("Golden Gate Park", "Presidio"): 11/60,
        ("Golden Gate Park", "Chinatown"): 23/60,
        ("Golden Gate Park", "Pacific Heights"): 16/60,
        ("Union Square", "Alamo Square"): 15/60,
        ("Union Square", "Presidio"): 24/60,
        ("Union Square", "Chinatown"): 7/60,
        ("Union Square", "Pacific Heights"): 15/60,
        ("Alamo Square", "Presidio"): 17/60,
        ("Alamo Square", "Chinatown"): 15/60,
        ("Alamo Square", "Pacific Heights"): 10/60,
        ("Presidio", "Chinatown"): 21/60,
        ("Presidio", "Pacific Heights"): 11/60,
        ("Chinatown", "Pacific Heights"): 10/60
    }

    # Add symmetric travel times
    for (loc1, loc2), time in list(travel_times.items()):
        travel_times[(loc2, loc1)] = time

    # Create Z3 variables for each meeting
    meet_vars = {}
    for name in friends:
        meet_vars[name] = {
            "start": Real(f"start_{name}"),
            "end": Real(f"end_{name}"),
            "met": Bool(f"met_{name}")
        }

    # Current location starts at Bayview
    current_location = "Bayview"
    current_time = 9.0  # 9:00 AM

    # Meet Matthew first if possible
    matthew = friends["Matthew"]
    opt.add(meet_vars["Matthew"]["start"] == 8.25)
    opt.add(meet_vars["Matthew"]["end"] == 8.5)
    opt.add(meet_vars["Matthew"]["met"] == True)

    # After meeting Matthew, update current time and location
    current_time = 8.5
    current_location = "Presidio"

    # Define constraints for each friend
    for name in friends:
        if name == "Matthew":
            continue  # already handled
        friend = friends[name]
        start = meet_vars[name]["start"]
        end = meet_vars[name]["end"]
        met = meet_vars[name]["met"]

        # Meeting must be within friend's availability
        opt.add(Implies(met, start >= friend["start"]))
        opt.add(Implies(met, end <= friend["end"]))
        opt.add(Implies(met, end == start + friend["duration"]))

        # Ensure meeting doesn't overlap with others
        for other in friends:
            if other == name:
                continue
            other_start = meet_vars[other]["start"]
            other_end = meet_vars[other]["end"]
            other_met = meet_vars[other]["met"]
            opt.add(Implies(And(met, other_met), Or(end <= other_start, start >= other_end)))

    # Travel time constraints
    for name1 in friends:
        for name2 in friends:
            if name1 == name2:
                continue
            loc1 = friends[name1]["location"]
            loc2 = friends[name2]["location"]
            travel_time = travel_times.get((loc1, loc2), 0)
            opt.add(Implies(
                And(meet_vars[name1]["met"], meet_vars[name2]["met"]),
                meet_vars[name2]["start"] >= meet_vars[name1]["end"] + travel_time
            ))

    # Maximize the number of friends met
    total_met = Sum([If(meet_vars[name]["met"], 1, 0) for name in friends])
    opt.maximize(total_met)

    # Initialize itinerary
    itinerary = []

    # Solve the problem
    if opt.check() == sat:
        model = opt.model()
        for name in friends:
            if is_true(model[meet_vars[name]["met"]]):
                start = model[meet_vars[name]["start"]]
                end = model[meet_vars[name]["end"]]
                start_time = float(start.numerator_as_long())/float(start.denominator_as_long())
                end_time = float(end.numerator_as_long())/float(end.denominator_as_long())
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{int(start_time):02d}:{int((start_time % 1) * 60):02d}",
                    "end_time": f"{int(end_time):02d}:{int((end_time % 1) * 60):02d}"
                })
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x["start_time"][:2]), int(x["start_time"][3:5])))
    else:
        itinerary = []  # No solution found

    return {"itinerary": itinerary}

# Run the solver and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))