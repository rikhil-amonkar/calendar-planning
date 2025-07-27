from z3 import *
import json

def solve_scheduling():
    opt = Optimize()

    # Define friends and their details
    friends = [
        {"name": "Paul", "location": "Nob Hill", "start": 975, "end": 1275, "min_duration": 60},
        {"name": "Carol", "location": "Union Square", "start": 1080, "end": 1215, "min_duration": 120},
        {"name": "Patricia", "location": "Chinatown", "start": 1200, "end": 1290, "min_duration": 75},
        {"name": "Karen", "location": "The Castro", "start": 1020, "end": 1140, "min_duration": 45},
        {"name": "Nancy", "location": "Presidio", "start": 705, "end": 1320, "min_duration": 30},
        {"name": "Jeffrey", "location": "Pacific Heights", "start": 1200, "end": 1245, "min_duration": 45},
        {"name": "Matthew", "location": "Russian Hill", "start": 945, "end": 1305, "min_duration": 75}
    ]

    # Travel times dictionary
    travel_times = {
        "Bayview": {"Nob Hill": 20, "Union Square": 17, "Chinatown": 18, "The Castro": 20, "Presidio": 31, "Pacific Heights": 23, "Russian Hill": 23},
        "Nob Hill": {"Bayview": 19, "Union Square": 7, "Chinatown": 6, "The Castro": 17, "Presidio": 17, "Pacific Heights": 8, "Russian Hill": 5},
        "Union Square": {"Bayview": 15, "Nob Hill": 9, "Chinatown": 7, "The Castro": 19, "Presidio": 24, "Pacific Heights": 15, "Russian Hill": 13},
        "Chinatown": {"Bayview": 22, "Nob Hill": 8, "Union Square": 7, "The Castro": 22, "Presidio": 19, "Pacific Heights": 10, "Russian Hill": 7},
        "The Castro": {"Bayview": 19, "Nob Hill": 16, "Union Square": 19, "Chinatown": 20, "Presidio": 20, "Pacific Heights": 16, "Russian Hill": 18},
        "Presidio": {"Bayview": 31, "Nob Hill": 18, "Union Square": 22, "Chinatown": 21, "The Castro": 21, "Pacific Heights": 11, "Russian Hill": 14},
        "Pacific Heights": {"Bayview": 22, "Nob Hill": 8, "Union Square": 12, "Chinatown": 11, "The Castro": 16, "Presidio": 11, "Russian Hill": 7},
        "Russian Hill": {"Bayview": 23, "Nob Hill": 5, "Union Square": 11, "Chinatown": 9, "The Castro": 21, "Presidio": 14, "Pacific Heights": 7}
    }

    # Create variables
    meeting_starts = {f["name"]: Int(f"start_{f['name']}") for f in friends}
    meeting_ends = {f["name"]: Int(f"end_{f['name']}") for f in friends}
    meet_flags = {f["name"]: Bool(f"meet_{f['name']}") for f in friends}

    # Basic constraints
    for f in friends:
        opt.add(Implies(meet_flags[f["name"]], meeting_starts[f["name"]] >= f["start"]))
        opt.add(Implies(meet_flags[f["name"]], meeting_ends[f["name"]] <= f["end"]))
        opt.add(Implies(meet_flags[f["name"]], meeting_ends[f["name"]] - meeting_starts[f["name"]] >= f["min_duration"]))

    # Sequence modeling
    current_time = Int("current_time")
    current_location = String("current_location")
    opt.add(current_time == 540)  # Start at 9:00 AM (540 minutes)
    opt.add(current_location == "Bayview")

    # Track sequence
    for f in friends:
        opt.add(Implies(meet_flags[f["name"]], 
                      And(meeting_starts[f["name"]] >= current_time + travel_times[current_location][f["location"]],
                          current_time == meeting_ends[f["name"]],
                          current_location == f["location"])))

    # No overlapping meetings
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            fi = friends[i]
            fj = friends[j]
            opt.add(Implies(And(meet_flags[fi["name"]], meet_flags[fj["name"]]),
                          Or(meeting_ends[fi["name"]] + travel_times[fi["location"]][fj["location"]] <= meeting_starts[fj["name"]],
                             meeting_ends[fj["name"]] + travel_times[fj["location"]][fi["location"]] <= meeting_starts[fi["name"]])))

    # Maximize number of meetings
    opt.maximize(Sum([If(meet_flags[f["name"]], 1, 0) for f in friends]))

    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for f in friends:
            if is_true(model.eval(meet_flags[f["name"]])):
                start = model.eval(meeting_starts[f["name"]]).as_long()
                end = model.eval(meeting_ends[f["name"]]).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": f["name"],
                    "start_time": f"{start//60:02d}:{start%60:02d}",
                    "end_time": f"{end//60:02d}:{end%60:02d}"
                })
        itinerary.sort(key=lambda x: int(x["start_time"][:2])*60 + int(x["start_time"][3:]))
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))