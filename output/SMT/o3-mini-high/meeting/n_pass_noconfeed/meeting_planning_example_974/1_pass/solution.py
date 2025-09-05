from z3 import *
import json

def minutes_to_time(m):
    hr = m // 60
    mi = m % 60
    return f"{hr}:{mi:02d}"

def main():
    # Travel times in minutes between locations.
    travel = {
        "Sunset District": {
            "Presidio": 16,
            "Nob Hill": 27,
            "Pacific Heights": 21,
            "Mission District": 25,
            "Marina District": 21,
            "North Beach": 28,
            "Russian Hill": 24,
            "Richmond District": 12,
            "Embarcadero": 30,
            "Alamo Square": 17
        },
        "Presidio": {
            "Sunset District": 15,
            "Nob Hill": 18,
            "Pacific Heights": 11,
            "Mission District": 26,
            "Marina District": 11,
            "North Beach": 18,
            "Russian Hill": 14,
            "Richmond District": 7,
            "Embarcadero": 20,
            "Alamo Square": 19
        },
        "Nob Hill": {
            "Sunset District": 24,
            "Presidio": 17,
            "Pacific Heights": 8,
            "Mission District": 13,
            "Marina District": 11,
            "North Beach": 8,
            "Russian Hill": 5,
            "Richmond District": 14,
            "Embarcadero": 9,
            "Alamo Square": 11
        },
        "Pacific Heights": {
            "Sunset District": 21,
            "Presidio": 11,
            "Nob Hill": 8,
            "Mission District": 15,
            "Marina District": 6,
            "North Beach": 9,
            "Russian Hill": 7,
            "Richmond District": 12,
            "Embarcadero": 10,
            "Alamo Square": 10
        },
        "Mission District": {
            "Sunset District": 24,
            "Presidio": 25,
            "Nob Hill": 12,
            "Pacific Heights": 16,
            "Marina District": 19,
            "North Beach": 17,
            "Russian Hill": 15,
            "Richmond District": 20,
            "Embarcadero": 19,
            "Alamo Square": 11
        },
        "Marina District": {
            "Sunset District": 19,
            "Presidio": 10,
            "Nob Hill": 12,
            "Pacific Heights": 7,
            "Mission District": 20,
            "North Beach": 11,
            "Russian Hill": 8,
            "Richmond District": 11,
            "Embarcadero": 14,
            "Alamo Square": 15
        },
        "North Beach": {
            "Sunset District": 27,
            "Presidio": 17,
            "Nob Hill": 7,
            "Pacific Heights": 8,
            "Mission District": 18,
            "Marina District": 9,
            "Russian Hill": 4,
            "Richmond District": 18,
            "Embarcadero": 6,
            "Alamo Square": 16
        },
        "Russian Hill": {
            "Sunset District": 23,
            "Presidio": 14,
            "Nob Hill": 5,
            "Pacific Heights": 7,
            "Mission District": 16,
            "Marina District": 7,
            "North Beach": 5,
            "Richmond District": 14,
            "Embarcadero": 8,
            "Alamo Square": 15
        },
        "Richmond District": {
            "Sunset District": 11,
            "Presidio": 7,
            "Nob Hill": 17,
            "Pacific Heights": 10,
            "Mission District": 20,
            "Marina District": 9,
            "North Beach": 17,
            "Russian Hill": 13,
            "Embarcadero": 19,
            "Alamo Square": 13
        },
        "Embarcadero": {
            "Sunset District": 30,
            "Presidio": 20,
            "Nob Hill": 10,
            "Pacific Heights": 11,
            "Mission District": 20,
            "Marina District": 12,
            "North Beach": 5,
            "Russian Hill": 8,
            "Richmond District": 21,
            "Alamo Square": 19
        },
        "Alamo Square": {
            "Sunset District": 16,
            "Presidio": 17,
            "Nob Hill": 11,
            "Pacific Heights": 10,
            "Mission District": 10,
            "Marina District": 15,
            "North Beach": 15,
            "Russian Hill": 13,
            "Richmond District": 11,
            "Embarcadero": 16
        }
    }

    # Define friends and meeting constraints.
    # Times are in minutes after midnight.
    friends = [
        {"name": "Charles", "location": "Presidio", "avail_start": 13 * 60 + 15, "avail_end": 15 * 60, "duration": 105},
        {"name": "Robert", "location": "Nob Hill", "avail_start": 13 * 60 + 15, "avail_end": 17 * 60 + 30, "duration": 90},
        {"name": "Nancy", "location": "Pacific Heights", "avail_start": 14 * 60 + 45, "avail_end": 22 * 60, "duration": 105},
        {"name": "Brian", "location": "Mission District", "avail_start": 15 * 60 + 30, "avail_end": 22 * 60, "duration": 60},
        {"name": "Kimberly", "location": "Marina District", "avail_start": 17 * 60, "avail_end": 19 * 60 + 45, "duration": 75},
        {"name": "David", "location": "North Beach", "avail_start": 14 * 60 + 45, "avail_end": 16 * 60 + 30, "duration": 75},
        {"name": "William", "location": "Russian Hill", "avail_start": 12 * 60 + 30, "avail_end": 19 * 60 + 15, "duration": 120},
        {"name": "Jeffrey", "location": "Richmond District", "avail_start": 12 * 60, "avail_end": 19 * 60 + 15, "duration": 45},
        {"name": "Karen", "location": "Embarcadero", "avail_start": 14 * 60 + 15, "avail_end": 20 * 60 + 45, "duration": 60},
        {"name": "Joshua", "location": "Alamo Square", "avail_start": 18 * 60 + 45, "avail_end": 22 * 60, "duration": 60}
    ]
    
    # Arrival: you arrive at Sunset District at 9:00 (540 minutes).
    start_location = "Sunset District"
    arrival_time = 9 * 60  # 9:00 AM

    opt = Optimize()
    n = len(friends)

    # Boolean indicator if we schedule a meeting with friend i.
    meet_vars = [Bool(f"meet_{i}") for i in range(n)]
    # Start time of meeting i.
    start_vars = [Int(f"start_{i}") for i in range(n)]

    # Add constraints for each meeting if scheduled.
    for i, friend in enumerate(friends):
        # The meeting must start no earlier than the friend's available start
        opt.add(Implies(meet_vars[i], start_vars[i] >= friend["avail_start"]))
        # And finish (start + duration) no later than the friend's available end.
        opt.add(Implies(meet_vars[i], start_vars[i] + friend["duration"] <= friend["avail_end"]))
        # Also, you must be able to travel from the sunset district (your starting point) to the meeting location.
        opt.add(Implies(meet_vars[i], start_vars[i] >= arrival_time + travel[start_location][friend["location"]]))

    # Add pairwise ordering/travel constraints for any two scheduled meetings.
    for i in range(n):
        for j in range(i+1, n):
            travel_i_j = travel[friends[i]["location"]][friends[j]["location"]]
            travel_j_i = travel[friends[j]["location"]][friends[i]["location"]]
            # If both meetings are scheduled, then either meeting i happens before j or vice versa.
            opt.add(Implies(
                And(meet_vars[i], meet_vars[j]),
                Or(
                    start_vars[i] + friends[i]["duration"] + travel_i_j <= start_vars[j],
                    start_vars[j] + friends[j]["duration"] + travel_j_i <= start_vars[i]
                )
            ))

    # Define the objective: maximize the total number of meetings scheduled.
    total_meetings = Sum([If(meet_vars[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)

    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for i, friend in enumerate(friends):
            if is_true(model.evaluate(meet_vars[i])):
                s = model.evaluate(start_vars[i]).as_long()
                e = s + friend["duration"]
                scheduled.append({
                    "person": friend["name"],
                    "location": friend["location"],
                    "start": s,
                    "end": e
                })
        # Sort the meetings in chronological order
        scheduled.sort(key=lambda m: m["start"])
        itinerary = []
        for event in scheduled:
            itinerary.append({
                "action": "meet",
                "location": event["location"],
                "person": event["person"],
                "start_time": minutes_to_time(event["start"]),
                "end_time": minutes_to_time(event["end"])
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()