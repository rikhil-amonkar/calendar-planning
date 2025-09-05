from z3 import *
import json

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Friend meeting parameters: available window (in minutes since midnight) and minimum meeting duration.
    friends = [
        {"name": "Betty", "location": "Russian Hill", "avail_start": 420, "avail_end": 1005, "min_dur": 105},
        {"name": "Melissa", "location": "Alamo Square", "avail_start": 570, "avail_end": 1035, "min_dur": 105},
        {"name": "Joshua", "location": "Haight-Ashbury", "avail_start": 735, "avail_end": 1140, "min_dur": 90},
        {"name": "Jeffrey", "location": "Marina District", "avail_start": 735, "avail_end": 1080, "min_dur": 45},
        {"name": "James", "location": "Bayview", "avail_start": 450, "avail_end": 1200, "min_dur": 90},
        {"name": "Anthony", "location": "Chinatown", "avail_start": 705, "avail_end": 810, "min_dur": 75},
        {"name": "Timothy", "location": "Presidio", "avail_start": 750, "avail_end": 885, "min_dur": 90},
        {"name": "Emily", "location": "Sunset District", "avail_start": 1170, "avail_end": 1290, "min_dur": 120}
    ]
    
    # Travel times in minutes between locations.
    travel = {
        "Union Square": {
            "Russian Hill": 13,
            "Alamo Square": 15,
            "Haight-Ashbury": 18,
            "Marina District": 18,
            "Bayview": 15,
            "Chinatown": 7,
            "Presidio": 24,
            "Sunset District": 27
        },
        "Russian Hill": {
            "Union Square": 10,
            "Alamo Square": 15,
            "Haight-Ashbury": 17,
            "Marina District": 7,
            "Bayview": 23,
            "Chinatown": 9,
            "Presidio": 14,
            "Sunset District": 23
        },
        "Alamo Square": {
            "Union Square": 14,
            "Russian Hill": 13,
            "Haight-Ashbury": 5,
            "Marina District": 15,
            "Bayview": 16,
            "Chinatown": 15,
            "Presidio": 17,
            "Sunset District": 16
        },
        "Haight-Ashbury": {
            "Union Square": 19,
            "Russian Hill": 17,
            "Alamo Square": 5,
            "Marina District": 17,
            "Bayview": 18,
            "Chinatown": 19,
            "Presidio": 15,
            "Sunset District": 15
        },
        "Marina District": {
            "Union Square": 16,
            "Russian Hill": 8,
            "Alamo Square": 15,
            "Haight-Ashbury": 16,
            "Bayview": 27,
            "Chinatown": 15,
            "Presidio": 10,
            "Sunset District": 19
        },
        "Bayview": {
            "Union Square": 18,
            "Russian Hill": 23,
            "Alamo Square": 16,
            "Haight-Ashbury": 19,
            "Marina District": 27,
            "Chinatown": 19,
            "Presidio": 32,
            "Sunset District": 23
        },
        "Chinatown": {
            "Union Square": 7,
            "Russian Hill": 7,
            "Alamo Square": 17,
            "Haight-Ashbury": 19,
            "Marina District": 12,
            "Bayview": 20,
            "Presidio": 19,
            "Sunset District": 29
        },
        "Presidio": {
            "Union Square": 22,
            "Russian Hill": 14,
            "Alamo Square": 19,
            "Haight-Ashbury": 15,
            "Marina District": 11,
            "Bayview": 31,
            "Chinatown": 21,
            "Sunset District": 15
        },
        "Sunset District": {
            "Union Square": 30,
            "Russian Hill": 24,
            "Alamo Square": 17,
            "Haight-Ashbury": 15,
            "Marina District": 21,
            "Bayview": 22,
            "Chinatown": 30,
            "Presidio": 16
        }
    }
    
    # You arrive at Union Square at 9:00AM (540 minutes after midnight)
    arrival_time = 540
    arrival_location = "Union Square"
    
    opt = Optimize()
    friend_vars = []
    
    # Create decision variables for each friend:
    # x: Boolean scheduled flag, s: meeting start time, e: meeting end time.
    for f in friends:
        name = f["name"]
        loc = f["location"]
        x = Bool("x_" + name)
        s = Int("s_" + name)
        e = Int("e_" + name)
        friend_vars.append((name, loc, f["avail_start"], f["avail_end"], f["min_dur"], x, s, e))
        
        # If the meeting is scheduled, enforce the friend's time window and minimum duration.
        opt.add(Implies(x, s >= f["avail_start"]))
        opt.add(Implies(x, e <= f["avail_end"]))
        opt.add(Implies(x, e - s >= f["min_dur"]))
        # Ensure arrival from Union Square is accounted for.
        opt.add(Implies(x, s >= arrival_time + travel[arrival_location][loc]))
    
    n = len(friend_vars)
    # Add pairwise constraints so that meetings do not overlap: if both meetings are scheduled then either one must finish (plus travel) before the other starts.
    for i in range(n):
        for j in range(i+1, n):
            name_i, loc_i, avail_start_i, avail_end_i, min_dur_i, x_i, s_i, e_i = friend_vars[i]
            name_j, loc_j, avail_start_j, avail_end_j, min_dur_j, x_j, s_j, e_j = friend_vars[j]
            travel_ij = travel[loc_i][loc_j]
            travel_ji = travel[loc_j][loc_i]
            opt.add(Implies(And(x_i, x_j),
                Or(
                    And(s_i <= s_j, s_j >= e_i + travel_ij),
                    And(s_j < s_i, s_i >= e_j + travel_ji)
                )
            ))
    
    # The objective is to maximize the total number of meetings scheduled.
    count_expr = Sum([If(x, 1, 0) for (_, _, _, _, _, x, _, _) in friend_vars])
    opt.maximize(count_expr)
    
    if opt.check() == sat:
        model = opt.model()
        schedule = []
        for (name, loc, avail_start, avail_end, min_dur, x, s, e) in friend_vars:
            if is_true(model.evaluate(x)):
                start_val = model.evaluate(s).as_long()
                end_val = model.evaluate(e).as_long()
                schedule.append({"person": name, "location": loc, "start": start_val, "end": end_val})
        # Sort meetings by start time.
        schedule.sort(key=lambda item: item["start"])
        itinerary = []
        for item in schedule:
            itinerary.append({
                "action": "meet",
                "location": item["location"],
                "person": item["person"],
                "start_time": minutes_to_time(item["start"]),
                "end_time": minutes_to_time(item["end"])
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))
        
if __name__ == "__main__":
    main()