import json
from z3 import *

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define friend meeting constraints and locations (times in minutes from midnight)
    # Note: Even if a friend is available earlier, you cannot start before your own arrival at 9:00 (which is 540 minutes)
    friends = [
        {"name": "Robert", "location": "Chinatown", "avail_start": 465, "avail_end": 1050, "min_meeting": 120},
        {"name": "David", "location": "Sunset District", "avail_start": 750, "avail_end": 1185, "min_meeting": 45},
        {"name": "Matthew", "location": "Alamo Square", "avail_start": 525, "avail_end": 825, "min_meeting": 90},
        {"name": "Jessica", "location": "Financial District", "avail_start": 570, "avail_end": 1125, "min_meeting": 45},
        {"name": "Melissa", "location": "North Beach", "avail_start": 435, "avail_end": 1005, "min_meeting": 45},
        {"name": "Mark", "location": "Embarcadero", "avail_start": 915, "avail_end": 1020, "min_meeting": 45},
        {"name": "Deborah", "location": "Presidio", "avail_start": 1140, "avail_end": 1185, "min_meeting": 45},
        {"name": "Karen", "location": "Golden Gate Park", "avail_start": 1170, "avail_end": 1320, "min_meeting": 120},
        {"name": "Laura", "location": "Bayview", "avail_start": 1275, "avail_end": 1335, "min_meeting": 15}
    ]

    # Define travel times (in minutes) from each location to every other location.
    travel_times = {
        "Richmond District": {
            "Chinatown": 20, "Sunset District": 11, "Alamo Square": 13, "Financial District": 22,
            "North Beach": 17, "Embarcadero": 19, "Presidio": 7, "Golden Gate Park": 9, "Bayview": 27
        },
        "Chinatown": {
            "Richmond District": 20, "Sunset District": 29, "Alamo Square": 17, "Financial District": 5,
            "North Beach": 3, "Embarcadero": 5, "Presidio": 19, "Golden Gate Park": 23, "Bayview": 20
        },
        "Sunset District": {
            "Richmond District": 12, "Chinatown": 30, "Alamo Square": 17, "Financial District": 30,
            "North Beach": 28, "Embarcadero": 30, "Presidio": 16, "Golden Gate Park": 11, "Bayview": 22
        },
        "Alamo Square": {
            "Richmond District": 11, "Chinatown": 15, "Sunset District": 16, "Financial District": 17,
            "North Beach": 15, "Embarcadero": 16, "Presidio": 17, "Golden Gate Park": 9, "Bayview": 16
        },
        "Financial District": {
            "Richmond District": 21, "Chinatown": 5, "Sunset District": 30, "Alamo Square": 17,
            "North Beach": 7, "Embarcadero": 4, "Presidio": 22, "Golden Gate Park": 23, "Bayview": 19
        },
        "North Beach": {
            "Richmond District": 18, "Chinatown": 6, "Sunset District": 27, "Alamo Square": 16,
            "Financial District": 8, "Embarcadero": 6, "Presidio": 17, "Golden Gate Park": 22, "Bayview": 25
        },
        "Embarcadero": {
            "Richmond District": 21, "Chinatown": 7, "Sunset District": 30, "Alamo Square": 19,
            "Financial District": 5, "North Beach": 5, "Presidio": 20, "Golden Gate Park": 25, "Bayview": 21
        },
        "Presidio": {
            "Richmond District": 7, "Chinatown": 21, "Sunset District": 15, "Alamo Square": 19,
            "Financial District": 23, "North Beach": 18, "Embarcadero": 20, "Golden Gate Park": 12, "Bayview": 31
        },
        "Golden Gate Park": {
            "Richmond District": 7, "Chinatown": 23, "Sunset District": 10, "Alamo Square": 9,
            "Financial District": 26, "North Beach": 23, "Embarcadero": 25, "Presidio": 11, "Bayview": 23
        },
        "Bayview": {
            "Richmond District": 25, "Chinatown": 19, "Sunset District": 23, "Alamo Square": 16,
            "Financial District": 19, "North Beach": 22, "Embarcadero": 19, "Presidio": 32, "Golden Gate Park": 22
        }
    }

    num_friends = len(friends)
    
    # Create an Optimize instance to maximize the number of meetings scheduled.
    opt = Optimize()

    # For each friend, we create decision variables:
    # scheduled[i]: whether to meet friend i
    # start_vars[i] and end_vars[i]: meeting start and end times (in minutes)
    # pos_vars[i]: the ordering position in our schedule (if scheduled; 0 if not scheduled)
    scheduled = [Bool(f"scheduled_{i}") for i in range(num_friends)]
    start_vars = [Int(f"start_{i}") for i in range(num_friends)]
    end_vars = [Int(f"end_{i}") for i in range(num_friends)]
    pos_vars = [Int(f"pos_{i}") for i in range(num_friends)]

    # Add constraints for each meeting if scheduled.
    for i, friend in enumerate(friends):
        # Effective earliest start: you arrive at Richmond District at 9:00 (540 minutes),
        # so even if friend is available earlier, you cannot start before 540.
        effective_start = max(540, friend["avail_start"])
        opt.add(Implies(scheduled[i], start_vars[i] >= effective_start))
        opt.add(Implies(scheduled[i], end_vars[i] <= friend["avail_end"]))
        opt.add(Implies(scheduled[i], end_vars[i] - start_vars[i] >= friend["min_meeting"]))
        # If scheduled, the ordering position is between 1 and num_friends.
        opt.add(Implies(scheduled[i], And(pos_vars[i] >= 1, pos_vars[i] <= num_friends)))
        # If not scheduled, set position to 0.
        opt.add(Implies(Not(scheduled[i]), pos_vars[i] == 0))

    # Ensure that among scheduled meetings, all ordering positions are unique.
    for i in range(num_friends):
        for j in range(i+1, num_friends):
            opt.add(Implies(And(scheduled[i], scheduled[j]), pos_vars[i] != pos_vars[j]))

    # Add ordering constraints between every pair of scheduled meetings.
    # If meeting i is scheduled before meeting j, then j's start time must be at least
    # meeting i's end time plus the travel time from i's location to j's location.
    for i in range(num_friends):
        for j in range(i+1, num_friends):
            travel_ij = travel_times[friends[i]["location"]][friends[j]["location"]]
            travel_ji = travel_times[friends[j]["location"]][friends[i]["location"]]
            opt.add(Implies(And(scheduled[i], scheduled[j], pos_vars[i] < pos_vars[j]),
                            start_vars[j] >= end_vars[i] + travel_ij))
            opt.add(Implies(And(scheduled[i], scheduled[j], pos_vars[i] > pos_vars[j]),
                            start_vars[i] >= end_vars[j] + travel_ji))

    # The first scheduled meeting must be reachable from your starting location (Richmond District at 9:00).
    for i in range(num_friends):
        travel_from_start = travel_times["Richmond District"][friends[i]["location"]]
        opt.add(Implies(And(scheduled[i], pos_vars[i] == 1),
                        start_vars[i] >= 540 + travel_from_start))

    # (Optional) Ensure meeting times are non-negative.
    for i in range(num_friends):
        opt.add(Implies(scheduled[i], start_vars[i] >= 0))
        opt.add(Implies(scheduled[i], end_vars[i] >= 0))

    # Objective: maximize the number of meetings scheduled.
    total_meetings = Sum([If(s, 1, 0) for s in scheduled])
    opt.maximize(total_meetings)

    if opt.check() == sat:
        model = opt.model()
        schedule = []
        # Collect scheduled meetings with their order.
        for i, friend in enumerate(friends):
            if is_true(model.evaluate(scheduled[i])):
                pos_val = model.evaluate(pos_vars[i]).as_long()
                start_val = model.evaluate(start_vars[i]).as_long()
                end_val = model.evaluate(end_vars[i]).as_long()
                schedule.append((pos_val, friend["location"], friend["name"], start_val, end_val))
        # Sort by the ordering position.
        schedule.sort(key=lambda x: x[0])
        itinerary = []
        for pos_val, location, name, start_val, end_val in schedule:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()