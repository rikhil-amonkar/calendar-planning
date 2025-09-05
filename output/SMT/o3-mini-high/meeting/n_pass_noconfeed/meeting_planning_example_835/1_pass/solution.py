from z3 import *
import json

def main():
    # Travel times (in minutes) between locations.
    travel = {
        "Pacific Heights": {
            "Golden Gate Park": 15, "The Castro": 16, "Bayview": 22, "Marina District": 6,
            "Union Square": 12, "Sunset District": 21, "Alamo Square": 10, "Financial District": 13,
            "Mission District": 15
        },
        "Golden Gate Park": {
            "Pacific Heights": 16, "The Castro": 13, "Bayview": 23, "Marina District": 16,
            "Union Square": 22, "Sunset District": 10, "Alamo Square": 9, "Financial District": 26,
            "Mission District": 17
        },
        "The Castro": {
            "Pacific Heights": 16, "Golden Gate Park": 11, "Bayview": 19, "Marina District": 21,
            "Union Square": 19, "Sunset District": 17, "Alamo Square": 8, "Financial District": 21,
            "Mission District": 7
        },
        "Bayview": {
            "Pacific Heights": 23, "Golden Gate Park": 22, "The Castro": 19, "Marina District": 27,
            "Union Square": 18, "Sunset District": 23, "Alamo Square": 16, "Financial District": 19,
            "Mission District": 13
        },
        "Marina District": {
            "Pacific Heights": 7, "Golden Gate Park": 18, "The Castro": 22, "Bayview": 27,
            "Union Square": 16, "Sunset District": 19, "Alamo Square": 15, "Financial District": 17,
            "Mission District": 20
        },
        "Union Square": {
            "Pacific Heights": 15, "Golden Gate Park": 22, "The Castro": 17, "Bayview": 15,
            "Marina District": 18, "Sunset District": 27, "Alamo Square": 15, "Financial District": 9,
            "Mission District": 14
        },
        "Sunset District": {
            "Pacific Heights": 21, "Golden Gate Park": 11, "The Castro": 17, "Bayview": 22,
            "Marina District": 21, "Union Square": 30, "Alamo Square": 17, "Financial District": 30,
            "Mission District": 25
        },
        "Alamo Square": {
            "Pacific Heights": 10, "Golden Gate Park": 9, "The Castro": 8, "Bayview": 16,
            "Marina District": 15, "Union Square": 14, "Sunset District": 16, "Financial District": 17,
            "Mission District": 10
        },
        "Financial District": {
            "Pacific Heights": 13, "Golden Gate Park": 23, "The Castro": 20, "Bayview": 19,
            "Marina District": 15, "Union Square": 9, "Sunset District": 30, "Alamo Square": 17,
            "Mission District": 17
        },
        "Mission District": {
            "Pacific Heights": 16, "Golden Gate Park": 17, "The Castro": 7, "Bayview": 14,
            "Marina District": 19, "Union Square": 15, "Sunset District": 24, "Alamo Square": 11,
            "Financial District": 15
        }
    }

    # Meeting information.
    # Times are converted to minutes from midnight.
    # 9:00 AM is 540; for example, 9:30 = 570, 12:15 = 735, etc.
    meetings = [
        {"person": "Helen", "location": "Golden Gate Park", "avail_start": 570, "avail_end": 735, "min_dur": 45},
        {"person": "Deborah", "location": "Bayview", "avail_start": 510, "avail_end": 720, "min_dur": 30},
        {"person": "Matthew", "location": "Marina District", "avail_start": 555, "avail_end": 855, "min_dur": 45},
        {"person": "Joseph", "location": "Union Square", "avail_start": 855, "avail_end": 1125, "min_dur": 120},
        {"person": "Rebecca", "location": "Financial District", "avail_start": 885, "avail_end": 975, "min_dur": 30},
        {"person": "Ronald", "location": "Sunset District", "avail_start": 960, "avail_end": 1245, "min_dur": 60},
        {"person": "Robert", "location": "Alamo Square", "avail_start": 1110, "avail_end": 1275, "min_dur": 120},
        {"person": "Elizabeth", "location": "Mission District", "avail_start": 1110, "avail_end": 1260, "min_dur": 120},
        {"person": "Steven", "location": "The Castro", "avail_start": 1215, "avail_end": 1320, "min_dur": 105}
    ]
    
    num_meetings = len(meetings)
    
    # Create an Optimize object to maximize the number of meetings.
    opt = Optimize()
    
    # Decision variables:
    # selected[i] indicates whether we schedule meeting i.
    # start[i] and end[i] are the start and end times (in minutes from midnight) if meeting i is scheduled.
    selected = [Bool(f"selected_{i}") for i in range(num_meetings)]
    start_vars = [Int(f"start_{i}") for i in range(num_meetings)]
    end_vars = [Int(f"end_{i}") for i in range(num_meetings)]
    
    # For each meeting, add constraints to enforce the availability window,
    # minimum duration, and that the meeting is reachable from the starting point (Pacific Heights at 9:00, i.e. 540)
    for i, m in enumerate(meetings):
        # If the meeting is selected:
        #   start time must be no earlier than the available start and must allow the minimum meeting duration.
        opt.add(Implies(selected[i], start_vars[i] >= m["avail_start"]))
        opt.add(Implies(selected[i], start_vars[i] + m["min_dur"] <= m["avail_end"]))
        opt.add(Implies(selected[i], end_vars[i] == start_vars[i] + m["min_dur"]))
        # To keep variables defined even if not selected, set start and end to 0 when not selected.
        opt.add(Implies(Not(selected[i]), start_vars[i] == 0))
        opt.add(Implies(Not(selected[i]), end_vars[i] == 0))
        
        # The meeting must be reachable from Pacific Heights.
        travel_time_from_PH = travel["Pacific Heights"][m["location"]]
        opt.add(Implies(selected[i], start_vars[i] >= 540 + travel_time_from_PH))
    
    # For every pair of meetings that are both scheduled, add a disjunctive ordering constraint.
    # That is, for any two meetings i and j (i < j), either:
    #   meeting i ends, then after travel from its location to j's, meeting j begins,
    # or meeting j ends, and after travel from its location to i's, meeting i begins.
    for i in range(num_meetings):
        for j in range(i+1, num_meetings):
            loc_i = meetings[i]["location"]
            loc_j = meetings[j]["location"]
            travel_i_j = travel[loc_i][loc_j]
            travel_j_i = travel[loc_j][loc_i]
            order_constraint = Or(
                end_vars[i] + travel_i_j <= start_vars[j],
                end_vars[j] + travel_j_i <= start_vars[i]
            )
            opt.add(Implies(And(selected[i], selected[j]), order_constraint))
    
    # Objective: maximize the total number of meetings scheduled.
    opt.maximize(Sum([If(selected[i], 1, 0) for i in range(num_meetings)]))
    
    # Solve the scheduling problem.
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        scheduled_meetings = []
        for i, m in enumerate(meetings):
            if is_true(model.evaluate(selected[i])):
                st = model.evaluate(start_vars[i]).as_long()
                et = model.evaluate(end_vars[i]).as_long()
                scheduled_meetings.append((st, et, m["location"], m["person"]))
        # Sort the meetings according to their start times.
        scheduled_meetings.sort(key=lambda x: x[0])
        
        # Function to format minutes as HH:MM (24-hour format with no leading zero for the hour)
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"
        
        for st, et, loc, person in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": person,
                "start_time": format_time(st),
                "end_time": format_time(et)
            })
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()