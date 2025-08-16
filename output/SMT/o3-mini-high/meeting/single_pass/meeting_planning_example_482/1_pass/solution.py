from z3 import *
import json

def minute_to_time_str(m):
    # Convert an integer minute (since midnight) into a "HH:MM" string in 24-hour format.
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def main():
    # --- Data Definitions ---
    # Friend info: location, availability (in minutes since midnight) and required meeting duration (minutes)
    # Times: 8:15 = 495, 8:30 = 510, 7:15 = 435, 7:30 = 450, 9:00 = 540, 10:15 = 615, 12:15 = 735, etc.
    friends = {
        "Stephanie": {
            "location": "Mission District",
            "avail_start": 495,   # 8:15
            "avail_end": 825,     # 13:45
            "duration": 90
        },
        "Sandra": {
            "location": "Bayview",
            "avail_start": 780,   # 13:00
            "avail_end": 1170,    # 19:30
            "duration": 15
        },
        "Richard": {
            "location": "Pacific Heights",
            "avail_start": 435,   # 7:15
            "avail_end": 615,     # 10:15
            "duration": 75
        },
        "Brian": {
            "location": "Russian Hill",
            "avail_start": 735,   # 12:15
            "avail_end": 960,     # 16:00
            "duration": 120
        },
        "Jason": {
            "location": "Fisherman's Wharf",
            "avail_start": 510,   # 8:30
            "avail_end": 1065,    # 17:45
            "duration": 60
        }
    }
    
    # Travel time (in minutes) between locations.
    travel = {
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Bayview"): 15,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Russian Hill"): 7
    }
    
    # We always start our day at Haight-Ashbury at 9:00AM (which is 540 minutes after midnight).
    start_location = "Haight-Ashbury"
    arrival_time = 540

    # --- Z3 Optimize Setup ---
    opt = Optimize()
    
    # For each friend we create:
    #   - A Boolean variable "sel" indicating if we schedule that meeting.
    #   - An integer variable "start" for the meeting start time (in minutes since midnight).
    friend_vars = {}
    for name, info in friends.items():
        sel = Bool(f"sel_{name}")
        s_time = Int(f"start_{name}")
        friend_vars[name] = {
            "selected": sel,
            "start": s_time,
            "duration": info["duration"],
            "avail_start": info["avail_start"],
            "avail_end": info["avail_end"],
            "location": info["location"]
        }
        # Constraint: if this meeting is scheduled, then its start time must be no earlier than
        # (a) the friend’s available start AND
        # (b) the time needed to travel from our starting location.
        lb_from_start = arrival_time + travel[(start_location, info["location"])]
        opt.add(Implies(sel, s_time >= info["avail_start"]))
        opt.add(Implies(sel, s_time >= lb_from_start))
        # Also, the meeting must finish before the friend’s available end.
        opt.add(Implies(sel, s_time + info["duration"] <= info["avail_end"]))
    
    # For any two scheduled meetings, ensure the meetings do not overlap in time,
    # taking into account the travel time needed between their locations.
    names = list(friends.keys())
    for i in range(len(names)):
        for j in range(i+1, len(names)):
            name_i = names[i]
            name_j = names[j]
            var_i = friend_vars[name_i]
            var_j = friend_vars[name_j]
            # Get travel times between the two friends' locations.
            travel_i_j = travel[(var_i["location"], var_j["location"])]
            travel_j_i = travel[(var_j["location"], var_i["location"])]
            # Constraint: if both meetings are scheduled then either
            # meeting i finishes + travel time to j <= meeting j start
            # OR meeting j finishes + travel time to i <= meeting i start.
            opt.add(Or(
                Not(And(var_i["selected"], var_j["selected"])),
                var_i["start"] + var_i["duration"] + travel_i_j <= var_j["start"],
                var_j["start"] + var_j["duration"] + travel_j_i <= var_i["start"]
            ))
    
    # --- Objective: Maximize the number of meetings scheduled ---
    total_meetings = Sum([If(friend_vars[name]["selected"], 1, 0) for name in names])
    opt.maximize(total_meetings)
    
    # --- Check and Extract a Model ---
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        # Collect scheduled meetings with their start and end times, according to the model.
        for name in names:
            if is_true(model.evaluate(friend_vars[name]["selected"])):
                start_val = model.evaluate(friend_vars[name]["start"]).as_long()
                duration = friend_vars[name]["duration"]
                scheduled.append((name, start_val, start_val + duration))
        # Sort the scheduled meetings in chronological order.
        scheduled.sort(key=lambda x: x[1])
        
        # Build the itinerary in the required JSON format.
        itinerary = []
        for name, s, e in scheduled:
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minute_to_time_str(s),
                "end_time": minute_to_time_str(e)
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")
    
if __name__ == "__main__":
    main()