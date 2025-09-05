from z3 import *
import json

def minutes_to_str(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times (in minutes) as given in the problem.
    travel_times = {
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Russian Hill"): 18,
        
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Russian Hill"): 14,
        
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Mission District"): 24,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Russian Hill"): 24,
        
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Russian Hill"): 17,
        
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Russian Hill"): 15,
        
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Russian Hill"): 19,
        
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Golden Gate Park"): 21,
    }
    
    # Meeting information for each friend:
    # Times are in minutes from midnight.
    meetings = [
        {
            "person": "Rebecca",
            "location": "Presidio",
            "avail_start": 18 * 60 + 15,   # 18:15 -> 1095
            "avail_end": 20 * 60 + 45,     # 20:45 -> 1245
            "min_duration": 60
        },
        {
            "person": "Linda",
            "location": "Sunset District",
            "avail_start": 15 * 60 + 30,   # 15:30 -> 930
            "avail_end": 19 * 60 + 45,     # 19:45 -> 1185
            "min_duration": 30
        },
        {
            "person": "Elizabeth",
            "location": "Haight-Ashbury",
            "avail_start": 17 * 60 + 15,   # 17:15 -> 1035
            "avail_end": 19 * 60 + 30,     # 19:30 -> 1170
            "min_duration": 105
        },
        {
            "person": "William",
            "location": "Mission District",
            "avail_start": 13 * 60 + 15,   # 13:15 -> 795
            "avail_end": 19 * 60 + 30,     # 19:30 -> 1170
            "min_duration": 30
        },
        {
            "person": "Robert",
            "location": "Golden Gate Park",
            "avail_start": 14 * 60 + 15,   # 14:15 -> 855
            "avail_end": 21 * 60 + 30,     # 21:30 -> 1290
            "min_duration": 45
        },
        {
            "person": "Mark",
            "location": "Russian Hill",
            "avail_start": 10 * 60,        # 10:00 -> 600
            "avail_end": 21 * 60 + 15,       # 21:15 -> 1275
            "min_duration": 75
        }
    ]
    
    n = len(meetings)
    # Starting point: "The Castro" at 9:00 (9*60 = 540)
    start_loc = "The Castro"
    start_time = 9 * 60  # 540 minutes
    
    opt = Optimize()

    # Decision variables: for each meeting i,
    # scheduled[i] : Bool if the meeting is selected.
    # s[i] : start time of meeting i (if scheduled)
    # e[i] : end time of meeting i (if scheduled, e[i] == s[i] + min_duration)
    # order[i] : ordering number (if scheduled, a positive integer; unscheduled means 0)
    scheduled = [Bool(f"scheduled_{i}") for i in range(n)]
    s_vars = [Int(f"s_{i}") for i in range(n)]
    e_vars = [Int(f"e_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]
    
    # Add domain constraints for order variables and link to "scheduled"
    for i in range(n):
        opt.add(order_vars[i] >= 0, order_vars[i] <= n)
        # If scheduled then order > 0; if not scheduled then order == 0.
        opt.add(scheduled[i] == (order_vars[i] > 0))
    
    # Meeting time constraints for each scheduled meeting.
    for i, m in enumerate(meetings):
        avail_start = m["avail_start"]
        avail_end = m["avail_end"]
        dur = m["min_duration"]
        # If meeting is scheduled, its start time must respect availability.
        opt.add(Implies(scheduled[i], s_vars[i] >= avail_start))
        # Meeting must finish by avail_end.
        opt.add(Implies(scheduled[i], s_vars[i] + dur <= avail_end))
        # Define end time as start time plus duration (if scheduled).
        opt.add(Implies(scheduled[i], e_vars[i] == s_vars[i] + dur))
    
    # Travel constraints between meetings in order.
    # For any two meetings i and j that are both scheduled and ordered i before j,
    # the start time of j must be at least the finish time of i plus travel time.
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            # Only enforce if both meetings are scheduled and order[i] < order[j]
            # Use travel time from meetings[i]["location"] to meetings[j]["location"].
            loc_i = meetings[i]["location"]
            loc_j = meetings[j]["location"]
            if (loc_i, loc_j) not in travel_times:
                continue  # if missing, skip (should not happen)
            travel_time_ij = travel_times[(loc_i, loc_j)]
            opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[i] < order_vars[j]),
                            s_vars[j] >= e_vars[i] + travel_time_ij))
    
    # For the first scheduled meeting, include traveling from the starting location.
    for i in range(n):
        loc_i = meetings[i]["location"]
        if (start_loc, loc_i) not in travel_times:
            continue
        travel_from_start = travel_times[(start_loc, loc_i)]
        opt.add(Implies(And(scheduled[i], order_vars[i] == 1),
                        s_vars[i] >= start_time + travel_from_start))
    
    # Ensure that scheduled meetings have unique order numbers (ignoring unscheduled which have order 0).
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(scheduled[i], scheduled[j]),
                            order_vars[i] != order_vars[j]))
    
    # Objective: maximize the number of scheduled meetings.
    obj = Sum([If(scheduled[i], 1, 0) for i in range(n)])
    h = opt.maximize(obj)
    
    if opt.check() == sat:
        mod = opt.model()
        scheduled_meetings = []
        for i, m in enumerate(meetings):
            if is_true(mod.evaluate(scheduled[i])):
                order_val = mod.evaluate(order_vars[i]).as_long()
                start_val = mod.evaluate(s_vars[i]).as_long()
                end_val = mod.evaluate(e_vars[i]).as_long()
                scheduled_meetings.append({
                    "person": m["person"],
                    "location": m["location"],
                    "start": start_val,
                    "end": end_val,
                    "order": order_val
                })
        
        # Sort meetings by their order (lowest order first)
        scheduled_meetings.sort(key=lambda x: x["order"])
        
        # Build itinerary output
        itinerary = []
        for meeting in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_str(meeting["start"]),
                "end_time": minutes_to_str(meeting["end"])
            })
        
        result = {
            "itinerary": itinerary
        }
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()