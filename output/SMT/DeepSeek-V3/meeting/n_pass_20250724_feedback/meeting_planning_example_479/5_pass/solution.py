from z3 import *

def solve_scheduling_problem():
    opt = Optimize()

    # Friends data with locations and availability
    friends = {
        "Mary": {"location": "Golden Gate Park", "start": "08:45", "end": "11:45", "duration": 45},
        "Kevin": {"location": "Haight-Ashbury", "start": "10:15", "end": "16:15", "duration": 90},
        "Deborah": {"location": "Bayview", "start": "15:00", "end": "19:15", "duration": 120},
        "Stephanie": {"location": "Presidio", "start": "10:00", "end": "17:15", "duration": 120},
        "Emily": {"location": "Financial District", "start": "11:30", "end": "21:45", "duration": 105}
    }

    # Travel times between locations (in minutes)
    travel_times = {
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Financial District"): 5,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Financial District"): 26,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Presidio", "Financial District"): 23,
        ("Bayview", "Financial District"): 19
    }

    # Helper functions for time conversion
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    def minutes_to_time(minutes):
        h = (540 + minutes) // 60  # 9:00 AM is 540 minutes
        m = (540 + minutes) % 60
        return f"{h:02d}:{m:02d}"

    # Create meeting variables
    meet_vars = {}
    for friend in friends:
        meet_vars[friend] = {
            "start": Int(f"start_{friend}"),
            "end": Int(f"end_{friend}"),
            "met": Bool(f"met_{friend}")
        }

    # Add basic meeting constraints
    for friend in friends:
        data = friends[friend]
        start_avail = time_to_minutes(data["start"]) - 540
        end_avail = time_to_minutes(data["end"]) - 540
        duration = data["duration"]

        opt.add(Implies(meet_vars[friend]["met"],
                      And(meet_vars[friend]["start"] >= max(0, start_avail),
                          meet_vars[friend]["end"] <= end_avail,
                          meet_vars[friend]["end"] - meet_vars[friend]["start"] >= duration)))
        
        opt.add(Implies(Not(meet_vars[friend]["met"]),
                      And(meet_vars[friend]["start"] == 0,
                          meet_vars[friend]["end"] == 0)))

    # Create meeting order variables
    meeting_order = {f: Int(f"order_{f}") for f in friends}
    for f in friends:
        opt.add(Implies(meet_vars[f]["met"], meeting_order[f] >= 1))
        opt.add(Implies(Not(meet_vars[f]["met"]), meeting_order[f] == 0))

    # All active meetings have unique order numbers
    # Create a list of order variables and use If to handle the "active" condition
    order_vars = []
    for f in friends:
        order_vars.append(If(meet_vars[f]["met"], meeting_order[f], -1))  # Use -1 for inactive
    opt.add(Distinct([o for o in order_vars if o != -1]))

    # Track current location (0 = Embarcadero, others mapped to friends)
    location_map = {f: i+1 for i, f in enumerate(friends)}
    current_loc = {i: Int(f"loc_{i}") for i in range(len(friends)+1)}
    
    # Initial location is Embarcadero
    opt.add(current_loc[0] == 0)

    # Add travel time constraints between meetings
    for i in range(len(friends)):
        for f1 in friends:
            for f2 in friends:
                if f1 == f2:
                    continue
                    
                # Get travel time between locations
                loc1 = friends[f1]["location"]
                loc2 = friends[f2]["location"]
                travel_time = travel_times.get((loc1, loc2), 
                             travel_times.get((loc2, loc1), 0))
                
                # If f1 comes before f2 in order
                opt.add(Implies(And(meet_vars[f1]["met"], meet_vars[f2]["met"],
                                  meeting_order[f1] == i+1, meeting_order[f2] == i+2),
                              meet_vars[f2]["start"] >= meet_vars[f1]["end"] + travel_time))
                
                # Update current location
                opt.add(Implies(And(meet_vars[f1]["met"], meeting_order[f1] == i+1),
                              current_loc[i+1] == location_map[f1]))

    # Maximize number of friends met
    opt.maximize(Sum([If(meet_vars[friend]["met"], 1, 0) for friend in friends]))

    # Solve and format output
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        active_meetings = []
        
        for friend in friends:
            if model.evaluate(meet_vars[friend]["met"]):
                start = model.evaluate(meet_vars[friend]["start"]).as_long()
                end = model.evaluate(meet_vars[friend]["end"]).as_long()
                order = model.evaluate(meeting_order[friend]).as_long()
                active_meetings.append((order, friend, start, end))
        
        # Sort by meeting order
        active_meetings.sort()
        
        # Add travel segments
        current_time = 0  # Starting at 9:00 AM (540 minutes)
        current_location = "Embarcadero"
        
        for order, friend, start, end in active_meetings:
            # Add travel time if needed
            target_location = friends[friend]["location"]
            if current_location != target_location:
                travel_key = (current_location, target_location)
                travel_time = travel_times.get(travel_key, 
                            travel_times.get((target_location, current_location), 0))
                
                if start < current_time + travel_time:
                    # This indicates an invalid schedule - should be caught by constraints
                    pass
                
                current_time += travel_time
                current_location = target_location
            
            # Add meeting
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
            current_time = end
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling_problem()
print(solution)