from z3 import *
import json

# Convert minutes (since 9:00) to 24-hour time string (e.g., "9:00", "13:30")
def minutes_to_time(mins):
    hour = 9 + (mins // 60)
    minute = mins % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times (in minutes) between locations; keys are (from, to)
    travel_times = {
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Bayview"): 27,
        
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Bayview"): 19,
        
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Bayview"): 19,
        
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Bayview"): 27,
        
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Bayview"): 22,
        
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Bayview"): 18,
        
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Bayview"): 14,
        
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Mission District"): 17,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Bayview"): 20,
        
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Bayview"): 23,
        
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Bayview"): 16,
        
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Alamo Square"): 16,
    }
    
    # Define friend meeting information.
    # All times are in minutes relative to 9:00AM.
    friends = [
        {"name": "Matthew", "location": "The Castro", "avail_start": 450, "avail_end": 660, "min": 45},
        {"name": "Rebecca", "location": "Nob Hill", "avail_start": 375, "avail_end": 615, "min": 105},
        {"name": "Brian", "location": "Marina District", "avail_start": 315, "avail_end": 780, "min": 30},
        {"name": "Emily", "location": "Pacific Heights", "avail_start": 135, "avail_end": 645, "min": 15},
        {"name": "Karen", "location": "Haight-Ashbury", "avail_start": 165, "avail_end": 510, "min": 30},
        {"name": "Stephanie", "location": "Mission District", "avail_start": 240, "avail_end": 405, "min": 75},
        {"name": "James", "location": "Chinatown", "avail_start": 330, "avail_end": 600, "min": 120},
        {"name": "Steven", "location": "Russian Hill", "avail_start": 300, "avail_end": 660, "min": 30},
        {"name": "Elizabeth", "location": "Alamo Square", "avail_start": 240, "avail_end": 495, "min": 120},
        {"name": "William", "location": "Bayview", "avail_start": 555, "avail_end": 675, "min": 90},
    ]
    
    n = len(friends)
    
    # Create an Optimize object
    opt = Optimize()
    
    # For each friend, create decision variables:
    #   meet_i: a Bool indicating if the meeting is scheduled.
    #   s_i: start time of the meeting (in minutes since 9:00).
    #   e_i: end time of the meeting.
    meet = [Bool(f"meet_{i}") for i in range(n)]
    s = [Int(f"s_{i}") for i in range(n)]
    e = [Int(f"e_{i}") for i in range(n)]
    
    # Domain constraints: restrict times to a reasonable day (0 to 1440 minutes)
    for i in range(n):
        opt.add(s[i] >= 0, s[i] <= 1440)
        opt.add(e[i] >= 0, e[i] <= 1440)
    
    # Add availability, minimum meeting duration, and initial travel constraints.
    # If a meeting is scheduled, then:
    #   s_i must be no earlier than the friend's availability and also not before arriving from Richmond District.
    #   e_i must be no later than the friend's availability end.
    #   The meeting duration (e_i - s_i) must be at least the required minimum.
    for i, friend in enumerate(friends):
        avail_start = friend["avail_start"]
        avail_end = friend["avail_end"]
        min_duration = friend["min"]
        location = friend["location"]
        travel_from_richmond = travel_times[("Richmond District", location)]
        opt.add(Implies(meet[i],
                        And(s[i] >= avail_start,
                            s[i] >= travel_from_richmond,
                            e[i] <= avail_end,
                            e[i] - s[i] >= min_duration)))
    
    # Add disjunctive (non-overlap with travel) constraints for any pair of scheduled meetings.
    for i in range(n):
        for j in range(i + 1, n):
            loc_i = friends[i]["location"]
            loc_j = friends[j]["location"]
            travel_ij = travel_times[(loc_i, loc_j)]
            travel_ji = travel_times[(loc_j, loc_i)]
            # If both meetings are scheduled then either meeting i finishes (with travel) before meeting j starts,
            # or meeting j finishes (with travel) before meeting i starts.
            opt.add(Implies(And(meet[i], meet[j]),
                            Or(e[i] + travel_ij <= s[j],
                               e[j] + travel_ji <= s[i])))
    
    # Objective: maximize the number of meetings scheduled.
    total_meetings = Sum([If(meet[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)
    
    # Solve the optimization problem.
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for i in range(n):
            if is_true(model.evaluate(meet[i])):
                start_val = model.evaluate(s[i]).as_long()
                end_val = model.evaluate(e[i]).as_long()
                scheduled.append({
                    "name": friends[i]["name"],
                    "location": friends[i]["location"],
                    "start": start_val,
                    "end": end_val
                })
        # Sort scheduled meetings by their start time
        scheduled.sort(key=lambda x: x["start"])
        
        itinerary = []
        for item in scheduled:
            itinerary.append({
                "action": "meet",
                "location": item["location"],
                "person": item["name"],
                "start_time": minutes_to_time(item["start"]),
                "end_time": minutes_to_time(item["end"])
            })
            
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        # In case no schedule is feasible.
        print(json.dumps({"itinerary": []}))
    
if __name__ == "__main__":
    main()