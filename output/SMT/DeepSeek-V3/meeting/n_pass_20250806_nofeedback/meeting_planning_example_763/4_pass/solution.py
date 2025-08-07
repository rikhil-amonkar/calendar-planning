from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver with optimization
    opt = Optimize()

    # Define the locations and their travel times (in minutes)
    locations = [
        "Chinatown", "Embarcadero", "Pacific Heights", "Russian Hill", 
        "Haight-Ashbury", "Golden Gate Park", "Fisherman's Wharf", 
        "Sunset District", "The Castro"
    ]

    # Travel times matrix (from_location, to_location) -> minutes
    travel_times = {
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "The Castro"): 22,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "The Castro"): 25,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "The Castro"): 16,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "The Castro"): 21,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "The Castro"): 13,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "The Castro"): 17,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Sunset District"): 17,
    }

    # Friends' availability and constraints
    friends = {
        "Richard": {"location": "Embarcadero", "start": 15*60 + 15, "end": 18*60 + 45, "duration": 90},
        "Mark": {"location": "Pacific Heights", "start": 15*60, "end": 17*60, "duration": 45},
        "Matthew": {"location": "Russian Hill", "start": 17*60 + 30, "end": 21*60, "duration": 90},
        "Rebecca": {"location": "Haight-Ashbury", "start": 14*60 + 45, "end": 18*60, "duration": 60},
        "Melissa": {"location": "Golden Gate Park", "start": 13*60 + 45, "end": 17*60 + 30, "duration": 90},
        "Margaret": {"location": "Fisherman's Wharf", "start": 14*60 + 45, "end": 20*60 + 15, "duration": 15},
        "Emily": {"location": "Sunset District", "start": 15*60 + 45, "end": 17*60, "duration": 45},
        "George": {"location": "The Castro", "start": 14*60, "end": 16*60 + 15, "duration": 75},
    }

    # Create variables for each meeting's start and end times
    meet_vars = {}
    for name in friends:
        meet_vars[name] = {
            "start": Int(f"start_{name}"),
            "end": Int(f"end_{name}"),
            "location": friends[name]["location"],
            "duration": friends[name]["duration"],
            "met": Bool(f"met_{name}")  # Whether we meet this friend
        }

    # Add constraints for each meeting
    for name in friends:
        friend = friends[name]
        var = meet_vars[name]
        
        # If we meet this friend, enforce time constraints
        opt.add(Implies(var["met"], var["start"] >= friend["start"]))
        opt.add(Implies(var["met"], var["end"] <= friend["end"]))
        opt.add(Implies(var["met"], var["end"] == var["start"] + var["duration"]))
        
        # If we don't meet, set times to 0
        opt.add(Implies(Not(var["met"]), var["start"] == 0))
        opt.add(Implies(Not(var["met"]), var["end"] == 0))

    # Ensure meetings do not overlap and travel time is accounted for
    names = list(friends.keys())
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            name1 = names[i]
            name2 = names[j]
            loc1 = meet_vars[name1]["location"]
            loc2 = meet_vars[name2]["location"]
            travel_time = travel_times[(loc1, loc2)]

            # If both meetings happen, enforce no overlap
            opt.add(Implies(And(meet_vars[name1]["met"], meet_vars[name2]["met"]),
                         Or(meet_vars[name1]["end"] + travel_time <= meet_vars[name2]["start"],
                            meet_vars[name2]["end"] + travel_time <= meet_vars[name1]["start"])))

    # Starting at Chinatown at 9:00 AM (540 minutes)
    # For each meeting, if it happens, ensure it starts after travel time from Chinatown
    for name in friends:
        loc = meet_vars[name]["location"]
        travel_time = travel_times[("Chinatown", loc)]
        opt.add(Implies(meet_vars[name]["met"], 
                       meet_vars[name]["start"] >= 9*60 + travel_time))

    # Maximize the number of friends met
    opt.maximize(Sum([If(var["met"], 1, 0) for var in meet_vars.values()]))

    # Try to find a solution
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for name in friends:
            var = meet_vars[name]
            if is_true(model[var["met"]]):
                start = model[var["start"]].as_long()
                end = model[var["end"]].as_long()
                start_time = f"{start // 60:02d}:{start % 60:02d}"
                end_time = f"{end // 60:02d}:{end % 60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling()
print(json.dumps(solution, indent=2))