#!/usr/bin/env python3
import json
from z3 import *

def minutes_to_time(m):
    m = int(m)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times between locations (in minutes)
    travel = {}
    travel[("Chinatown", "Embarcadero")] = 5
    travel[("Chinatown", "Pacific Heights")] = 10
    travel[("Chinatown", "Russian Hill")] = 7
    travel[("Chinatown", "Haight-Ashbury")] = 19
    travel[("Chinatown", "Golden Gate Park")] = 23
    travel[("Chinatown", "Fisherman's Wharf")] = 8
    travel[("Chinatown", "Sunset District")] = 29
    travel[("Chinatown", "The Castro")] = 22

    travel[("Embarcadero", "Chinatown")] = 7
    travel[("Embarcadero", "Pacific Heights")] = 11
    travel[("Embarcadero", "Russian Hill")] = 8
    travel[("Embarcadero", "Haight-Ashbury")] = 21
    travel[("Embarcadero", "Golden Gate Park")] = 25
    travel[("Embarcadero", "Fisherman's Wharf")] = 6
    travel[("Embarcadero", "Sunset District")] = 30
    travel[("Embarcadero", "The Castro")] = 25

    travel[("Pacific Heights", "Chinatown")] = 11
    travel[("Pacific Heights", "Embarcadero")] = 10
    travel[("Pacific Heights", "Russian Hill")] = 7
    travel[("Pacific Heights", "Haight-Ashbury")] = 11
    travel[("Pacific Heights", "Golden Gate Park")] = 15
    travel[("Pacific Heights", "Fisherman's Wharf")] = 13
    travel[("Pacific Heights", "Sunset District")] = 21
    travel[("Pacific Heights", "The Castro")] = 16

    travel[("Russian Hill", "Chinatown")] = 9
    travel[("Russian Hill", "Embarcadero")] = 8
    travel[("Russian Hill", "Pacific Heights")] = 7
    travel[("Russian Hill", "Haight-Ashbury")] = 17
    travel[("Russian Hill", "Golden Gate Park")] = 21
    travel[("Russian Hill", "Fisherman's Wharf")] = 7
    travel[("Russian Hill", "Sunset District")] = 23
    travel[("Russian Hill", "The Castro")] = 21

    travel[("Haight-Ashbury", "Chinatown")] = 19
    travel[("Haight-Ashbury", "Embarcadero")] = 20
    travel[("Haight-Ashbury", "Pacific Heights")] = 12
    travel[("Haight-Ashbury", "Russian Hill")] = 17
    travel[("Haight-Ashbury", "Golden Gate Park")] = 7
    travel[("Haight-Ashbury", "Fisherman's Wharf")] = 23
    travel[("Haight-Ashbury", "Sunset District")] = 15
    travel[("Haight-Ashbury", "The Castro")] = 6

    travel[("Golden Gate Park", "Chinatown")] = 23
    travel[("Golden Gate Park", "Embarcadero")] = 25
    travel[("Golden Gate Park", "Pacific Heights")] = 16
    travel[("Golden Gate Park", "Russian Hill")] = 19
    travel[("Golden Gate Park", "Haight-Ashbury")] = 7
    travel[("Golden Gate Park", "Fisherman's Wharf")] = 24
    travel[("Golden Gate Park", "Sunset District")] = 10
    travel[("Golden Gate Park", "The Castro")] = 13

    travel[("Fisherman's Wharf", "Chinatown")] = 12
    travel[("Fisherman's Wharf", "Embarcadero")] = 8
    travel[("Fisherman's Wharf", "Pacific Heights")] = 12
    travel[("Fisherman's Wharf", "Russian Hill")] = 7
    travel[("Fisherman's Wharf", "Haight-Ashbury")] = 22
    travel[("Fisherman's Wharf", "Golden Gate Park")] = 25
    travel[("Fisherman's Wharf", "Sunset District")] = 27
    travel[("Fisherman's Wharf", "The Castro")] = 27

    travel[("Sunset District", "Chinatown")] = 30
    travel[("Sunset District", "Embarcadero")] = 30
    travel[("Sunset District", "Pacific Heights")] = 21
    travel[("Sunset District", "Russian Hill")] = 24
    travel[("Sunset District", "Haight-Ashbury")] = 15
    travel[("Sunset District", "Golden Gate Park")] = 11
    travel[("Sunset District", "Fisherman's Wharf")] = 29
    travel[("Sunset District", "The Castro")] = 17

    travel[("The Castro", "Chinatown")] = 22
    travel[("The Castro", "Embarcadero")] = 22
    travel[("The Castro", "Pacific Heights")] = 16
    travel[("The Castro", "Russian Hill")] = 18
    travel[("The Castro", "Haight-Ashbury")] = 6
    travel[("The Castro", "Golden Gate Park")] = 11
    travel[("The Castro", "Fisherman's Wharf")] = 24
    travel[("The Castro", "Sunset District")] = 17

    # Define friend meeting constraints:
    # Each friend has a fixed meeting location, an availability window, and a minimum meeting duration.
    # Times are represented as minutes from midnight. For example, 9:00AM is 540.
    friends = [
        {"name": "Richard", "location": "Embarcadero", "avail_start": 915, "avail_end": 1125, "min_dur": 90},
        {"name": "Mark", "location": "Pacific Heights", "avail_start": 900, "avail_end": 1020, "min_dur": 45},
        {"name": "Matthew", "location": "Russian Hill", "avail_start": 1050, "avail_end": 1260, "min_dur": 90},
        {"name": "Rebecca", "location": "Haight-Ashbury", "avail_start": 885, "avail_end": 1080, "min_dur": 60},
        {"name": "Melissa", "location": "Golden Gate Park", "avail_start": 825, "avail_end": 1050, "min_dur": 90},
        {"name": "Margaret", "location": "Fisherman's Wharf", "avail_start": 885, "avail_end": 1215, "min_dur": 15},
        {"name": "Emily", "location": "Sunset District", "avail_start": 945, "avail_end": 1020, "min_dur": 45},
        {"name": "George", "location": "The Castro", "avail_start": 840, "avail_end": 975, "min_dur": 75}
    ]

    n = len(friends)

    # Create an Optimize object to maximize the number of meetings scheduled.
    opt = Optimize()

    # Create decision variables for each friend: whether to meet, and the start and end times of the meeting.
    meet_vars = [Bool(f"meet_{i}") for i in range(n)]
    start_vars = [Int(f"start_{i}") for i in range(n)]
    end_vars = [Int(f"end_{i}") for i in range(n)]

    for i, f in enumerate(friends):
        # If meeting i is scheduled then the meeting start must be no earlier than the friend's available start.
        opt.add(Implies(meet_vars[i], start_vars[i] >= f["avail_start"]))
        # The meeting must finish by the friend's available end.
        opt.add(Implies(meet_vars[i], end_vars[i] <= f["avail_end"]))
        # The meeting duration is exactly the minimum required (to allow maximum scheduling flexibility).
        opt.add(Implies(meet_vars[i], end_vars[i] == start_vars[i] + f["min_dur"]))
        # From your start at Chinatown (9:00AM = 540), ensure travel time is accounted for.
        opt.add(Implies(meet_vars[i], start_vars[i] >= 540 + travel[("Chinatown", f["location"])]))

    # For any two scheduled meetings, ensure that their times (plus travel between locations) do not conflict.
    for i in range(n):
        for j in range(i+1, n):
            loc_i = friends[i]["location"]
            loc_j = friends[j]["location"]
            travel_ij = travel[(loc_i, loc_j)]
            travel_ji = travel[(loc_j, loc_i)]
            opt.add(Implies(And(meet_vars[i], meet_vars[j]),
                            Or(end_vars[i] + travel_ij <= start_vars[j],
                               end_vars[j] + travel_ji <= start_vars[i])))

    # Set the optimization objective to maximize the total number of meetings.
    total_meetings = Sum([If(meet_vars[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)

    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for i in range(n):
            if model.evaluate(meet_vars[i]):
                s = model.evaluate(start_vars[i]).as_long()
                e = model.evaluate(end_vars[i]).as_long()
                scheduled_meetings.append({
                    "person": friends[i]["name"],
                    "location": friends[i]["location"],
                    "start": s,
                    "end": e
                })
        # Order the meetings by start time.
        scheduled_meetings.sort(key=lambda x: x["start"])
        itinerary = []
        for m in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": m["location"],
                "person": m["person"],
                "start_time": minutes_to_time(m["start"]),
                "end_time": minutes_to_time(m["end"])
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()