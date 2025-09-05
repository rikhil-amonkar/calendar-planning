from z3 import *
import json

def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define friends' meeting data and availabilities (times in minutes since midnight)
    # 9:00 = 540, 7:15 = 435, 10:00 = 600, etc.
    friends_data = {
        "Mary": {
            "location": "Pacific Heights",
            "avail_start": 600,   # 10:00
            "avail_end": 1140,    # 19:00
            "duration": 45
        },
        "Lisa": {
            "location": "Mission District",
            "avail_start": 1230,  # 20:30
            "avail_end": 1320,    # 22:00
            "duration": 75
        },
        "Betty": {
            "location": "Haight-Ashbury",
            "avail_start": 435,   # 7:15
            "avail_end": 1035,    # 17:15
            "duration": 90
        },
        "Charles": {
            "location": "Financial District",
            "avail_start": 675,   # 11:15
            "avail_end": 900,     # 15:00
            "duration": 120
        }
    }
    
    # Travel times in minutes between locations (as given)
    travel = {
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Financial District"): 19,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Financial District"): 13,
        ("Mission District", "Bayview"): 15,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Financial District"): 17,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Haight-Ashbury"): 19
    }
    
    # Initialize the Optimize solver
    opt = Optimize()
    
    # Create decision variables for each friend:
    # f: Boolean decision whether to meet the friend.
    # S: Start time of meeting (in minutes since midnight).
    # order: The position in the schedule (if not meeting, order will be -1).
    f_vars = {}
    S_vars = {}
    order_vars = {}
    friends = list(friends_data.keys())
    for person in friends:
        f_vars[person] = Bool(f"meet_{person}")
        S_vars[person] = Int(f"S_{person}")
        order_vars[person] = Int(f"order_{person}")
    
    # Add constraints for meeting availability and meeting duration
    for person in friends:
        info = friends_data[person]
        # if meeting is scheduled, meeting must be within available window.
        opt.add(Implies(f_vars[person],
                        And(S_vars[person] >= info["avail_start"],
                            S_vars[person] + info["duration"] <= info["avail_end"])))
        # Order variable: if meeting scheduled, order in [0,3]; if not, order == -1.
        opt.add(Implies(f_vars[person], And(order_vars[person] >= 0, order_vars[person] <= 3)))
        opt.add(Implies(Not(f_vars[person]), order_vars[person] == -1))
    
    # For scheduled meetings, ensure distinct order values.
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            p1 = friends[i]
            p2 = friends[j]
            opt.add(Implies(And(f_vars[p1], f_vars[p2]),
                            order_vars[p1] != order_vars[p2]))
    
    # Travel constraints between meetings:
    # If two meetings p and q are scheduled with order(p) < order(q)
    # then meeting q must start after meeting p ends plus travel time.
    for p in friends:
        for q in friends:
            if p == q:
                continue
            loc_p = friends_data[p]["location"]
            loc_q = friends_data[q]["location"]
            # Only add constraint if travel information exists between these locations.
            if (loc_p, loc_q) in travel:
                travel_time = travel[(loc_p, loc_q)]
                opt.add(Implies(And(f_vars[p], f_vars[q], order_vars[p] < order_vars[q]),
                                S_vars[q] >= S_vars[p] + friends_data[p]["duration"] + travel_time))
    
    # Constraint for the first meeting: travel from starting location "Bayview" to meeting location.
    # You arrive at Bayview at 9:00 (540).
    for person in friends:
        loc = friends_data[person]["location"]
        if ("Bayview", loc) in travel:
            travel_time = travel[("Bayview", loc)]
            opt.add(Implies(And(f_vars[person], order_vars[person] == 0),
                            S_vars[person] >= 540 + travel_time))
        else:
            # If somehow travel info is missing, just require meeting start >= 540.
            opt.add(Implies(And(f_vars[person], order_vars[person] == 0), S_vars[person] >= 540))
    
    # Our objective is to maximize the number of meetings (i.e., meet as many friends as possible)
    total_meetings = Sum([If(f_vars[person], 1, 0) for person in friends])
    h = opt.maximize(total_meetings)
    
    # Check and get model
    if opt.check() == sat:
        model = opt.model()
        
        # Collect scheduled meetings and sort them by their order in the itinerary.
        scheduled = []
        for person in friends:
            if is_true(model.evaluate(f_vars[person])):
                meeting_order = model.evaluate(order_vars[person]).as_long()
                start_time = model.evaluate(S_vars[person]).as_long()
                end_time = start_time + friends_data[person]["duration"]
                scheduled.append({
                    "person": person,
                    "location": friends_data[person]["location"],
                    "order": meeting_order,
                    "start": start_time,
                    "end": end_time
                })
        scheduled.sort(key=lambda x: x["order"])
        
        # Build the itinerary for JSON output.
        itinerary = []
        for meet in scheduled:
            itinerary.append({
                "action": "meet",
                "location": meet["location"],
                "person": meet["person"],
                "start_time": format_time(meet["start"]),
                "end_time": format_time(meet["end"])
            })
        
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()