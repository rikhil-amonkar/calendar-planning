from z3 import Optimize, Int, Bool, If, And, Or, Implies, sat
import json

def format_time(t):
    # t is minutes after 9:00 AM; add 9 hours (540 minutes) to get the actual time
    total = t + 540
    hour = total // 60
    minute = total % 60
    return f"{hour}:{minute:02d}"

def main():
    # Friend meeting data: all times are in minutes relative to 9:00 AM.
    # For instance, 9:00 AM -> 0 minutes, 10:15 AM -> 75 minutes, etc.
    friend_data = [
        {"name": "Laura", "location": "Alamo Square", "avail_start": 330, "avail_end": 435, "min_duration": 75},
        {"name": "Brian", "location": "Presidio", "avail_start": 75,  "avail_end": 480, "min_duration": 30},
        {"name": "Karen", "location": "Russian Hill", "avail_start": 540, "avail_end": 675, "min_duration": 90},
        {"name": "Stephanie", "location": "North Beach", "avail_start": 75, "avail_end": 420, "min_duration": 75},
        {"name": "Helen", "location": "Golden Gate Park", "avail_start": 150, "avail_end": 765, "min_duration": 120},
        # Sandra's original availability is 8:00AM to 15:15, but we cannot start before 9:00AM.
        {"name": "Sandra", "location": "Richmond District", "avail_start": 0, "avail_end": 375, "min_duration": 30},
        {"name": "Mary", "location": "Embarcadero", "avail_start": 465, "avail_end": 585, "min_duration": 120},
        {"name": "Deborah", "location": "Financial District", "avail_start": 600, "avail_end": 705, "min_duration": 105},
        # Elizabeth's availability is 08:30AM to 13:15, so effective start is at 9:00 AM (0 minutes).
        {"name": "Elizabeth", "location": "Marina District", "avail_start": 0, "avail_end": 255, "min_duration": 105}
    ]
    
    # Travel times in minutes between locations.
    # Note: Times are not symmetric.
    travel_times = {
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Marina District"): 19,
        
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Marina District"): 15,
        
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Marina District"): 11,
        
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Marina District"): 7,
        
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Marina District"): 9,
        
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Marina District"): 16,
        
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Marina District"): 9,
        
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Marina District"): 12,
        
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Marina District"): 15,
        
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Financial District"): 17
    }
    
    # Create an Optimize object and define variables for each meeting.
    opt = Optimize()
    n = len(friend_data)
    meets = [Bool(f"meet_{i}") for i in range(n)]
    starts = [Int(f"start_{i}") for i in range(n)]
    
    # For each friend, if the meeting is scheduled, enforce:
    # 1. The meeting start time must be no earlier than the friend's availability window,
    #    and also no earlier than the travel time required from the Mission District.
    # 2. The meeting (starting at start time and lasting min_duration) must finish before the end of the window.
    for i, friend in enumerate(friend_data):
        # Lower bound: the later of the friend's availability start and travel from Mission District.
        travel_from_start = travel_times[("Mission District", friend["location"])]
        lower_bound = max(friend["avail_start"], travel_from_start)
        upper_bound = friend["avail_end"] - friend["min_duration"]
        opt.add(Implies(meets[i], starts[i] >= lower_bound))
        opt.add(Implies(meets[i], starts[i] <= upper_bound))
        opt.add(Implies(meets[i], starts[i] + friend["min_duration"] <= friend["avail_end"]))
    
    # For any two scheduled meetings, impose a non-overlap constraint with travel time between them.
    for i in range(n):
        for j in range(i + 1, n):
            loc_i = friend_data[i]["location"]
            loc_j = friend_data[j]["location"]
            travel_ij = travel_times[(loc_i, loc_j)]
            travel_ji = travel_times[(loc_j, loc_i)]
            dur_i = friend_data[i]["min_duration"]
            dur_j = friend_data[j]["min_duration"]
            # If both meetings are scheduled, then either i happens before j or j before i.
            opt.add(Implies(And(meets[i], meets[j]),
                            Or(starts[i] + dur_i + travel_ij <= starts[j],
                               starts[j] + dur_j + travel_ji <= starts[i])))
    
    # Objective: maximize the number of meetings scheduled.
    total_meetings = sum([If(m, 1, 0) for m in meets])
    opt.maximize(total_meetings)
    
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for i, friend in enumerate(friend_data):
            if model.evaluate(meets[i]):
                s_time = model.evaluate(starts[i]).as_long()
                e_time = s_time + friend["min_duration"]
                scheduled.append({
                    "person": friend["name"],
                    "location": friend["location"],
                    "start": s_time,
                    "end": e_time
                })
        # Sort the scheduled meetings by start time.
        scheduled.sort(key=lambda x: x["start"])
        itinerary = []
        for meet in scheduled:
            itinerary.append({
                "action": "meet",
                "location": meet["location"],
                "person": meet["person"],
                "start_time": format_time(meet["start"]),
                "end_time": format_time(meet["end"])
            })
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()