import json
from z3 import *

def minutes_to_str(m):
    # Convert minutes (integer) to H:MM 24-hour format (no leading zeros)
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Travel times in minutes for every pair of locations
    travel = {
        "The Castro": {
            "Presidio": 20,
            "Sunset District": 17,
            "Haight-Ashbury": 6,
            "Mission District": 7,
            "Golden Gate Park": 11,
            "Russian Hill": 18
        },
        "Presidio": {
            "The Castro": 21,
            "Sunset District": 15,
            "Haight-Ashbury": 15,
            "Mission District": 26,
            "Golden Gate Park": 12,
            "Russian Hill": 14
        },
        "Sunset District": {
            "The Castro": 17,
            "Presidio": 16,
            "Haight-Ashbury": 15,
            "Mission District": 24,
            "Golden Gate Park": 11,
            "Russian Hill": 24
        },
        "Haight-Ashbury": {
            "The Castro": 6,
            "Presidio": 15,
            "Sunset District": 15,
            "Mission District": 11,
            "Golden Gate Park": 7,
            "Russian Hill": 17
        },
        "Mission District": {
            "The Castro": 7,
            "Presidio": 25,
            "Sunset District": 24,
            "Haight-Ashbury": 12,
            "Golden Gate Park": 17,
            "Russian Hill": 15
        },
        "Golden Gate Park": {
            "The Castro": 13,
            "Presidio": 11,
            "Sunset District": 10,
            "Haight-Ashbury": 7,
            "Mission District": 17,
            "Russian Hill": 19
        },
        "Russian Hill": {
            "The Castro": 21,
            "Presidio": 14,
            "Sunset District": 23,
            "Haight-Ashbury": 17,
            "Mission District": 16,
            "Golden Gate Park": 21
        }
    }
    
    # Friend meeting data: name, location, availability window (in minutes from midnight) and minimum meeting duration
    friends = [
        {"name": "Rebecca", "location": "Presidio", "avail_start": 18 * 60 + 15, "avail_end": 20 * 60 + 45, "min_dur": 60},
        {"name": "Linda", "location": "Sunset District", "avail_start": 15 * 60 + 30, "avail_end": 19 * 60 + 45, "min_dur": 30},
        {"name": "Elizabeth", "location": "Haight-Ashbury", "avail_start": 17 * 60 + 15, "avail_end": 19 * 60 + 30, "min_dur": 105},
        {"name": "William", "location": "Mission District", "avail_start": 13 * 60 + 15, "avail_end": 19 * 60 + 30, "min_dur": 30},
        {"name": "Robert", "location": "Golden Gate Park", "avail_start": 14 * 60 + 15, "avail_end": 21 * 60 + 30, "min_dur": 45},
        {"name": "Mark", "location": "Russian Hill", "avail_start": 10 * 60, "avail_end": 21 * 60 + 15, "min_dur": 75},
    ]
    
    # Starting point: you arrive at The Castro at 9:00AM (540 minutes)
    start_location = "The Castro"
    start_time = 9 * 60  # 9:00 in minutes

    # Create an Optimize object from Z3
    opt = Optimize()

    # Create variables for each friend:
    # s_vars: meeting start time, e_vars: meeting end time, meet_vars: Boolean decision if meeting is scheduled.
    s_vars = {}
    e_vars = {}
    meet_vars = {}
    for friend in friends:
        name = friend["name"]
        s_vars[name] = Int("s_" + name)
        e_vars[name] = Int("e_" + name)
        meet_vars[name] = Bool("meet_" + name)
    
    # Add individual constraints for each meeting if it is scheduled.
    for friend in friends:
        name = friend["name"]
        avail_start = friend["avail_start"]
        avail_end = friend["avail_end"]
        min_dur = friend["min_dur"]
        # If meeting is scheduled, meeting must start no earlier than the friend's availability,
        # end no later than the friend's availability, and last at least the minimum duration.
        opt.add(Implies(meet_vars[name], s_vars[name] >= avail_start))
        opt.add(Implies(meet_vars[name], e_vars[name] <= avail_end))
        opt.add(Implies(meet_vars[name], e_vars[name] - s_vars[name] >= min_dur))
        # Also, if scheduled, the meeting start time must be after you can reach the location
        travel_from_start = travel[start_location][friend["location"]]
        opt.add(Implies(meet_vars[name], s_vars[name] >= start_time + travel_from_start))
    
    # Add pairwise non-overlap constraints (including travel time between meeting locations)
    # For any two scheduled meetings, one must occur before the other (accounting for travel).
    n = len(friends)
    for i in range(n):
        for j in range(i + 1, n):
            name_i = friends[i]["name"]
            name_j = friends[j]["name"]
            loc_i = friends[i]["location"]
            loc_j = friends[j]["location"]
            travel_ij = travel[loc_i][loc_j]
            travel_ji = travel[loc_j][loc_i]
            opt.add(Implies(And(meet_vars[name_i], meet_vars[name_j]),
                            Or(e_vars[name_i] + travel_ij <= s_vars[name_j],
                               e_vars[name_j] + travel_ji <= s_vars[name_i])))
    
    # Objective: maximize the number of meetings scheduled.
    total_meetings = Sum([If(meet_vars[friend["name"]], 1, 0) for friend in friends])
    opt.maximize(total_meetings)
    
    # Solve the scheduling problem.
    if opt.check() == sat:
        model = opt.model()
    else:
        print(json.dumps({"itinerary": []}))
        return

    # Extract scheduled meetings from the model and sort them by start time.
    itinerary_meetings = []
    for friend in friends:
        name = friend["name"]
        if is_true(model.evaluate(meet_vars[name])):
            s_val = model.evaluate(s_vars[name]).as_long()
            e_val = model.evaluate(e_vars[name]).as_long()
            itinerary_meetings.append({
                "name": name,
                "location": friend["location"],
                "s": s_val,
                "e": e_val
            })
    itinerary_meetings.sort(key=lambda m: m["s"])

    # Build the final itinerary following the required JSON structure.
    itinerary = []
    for meeting in itinerary_meetings:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["name"],
            "start_time": minutes_to_str(meeting["s"]),
            "end_time": minutes_to_str(meeting["e"])
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()