from z3 import *
import json

def format_time(t):
    # Convert minutes since midnight to "H:MM" format (24-hour, no leading zero for hour)
    hours = t // 60
    minutes = t % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Travel times (in minutes) between locations
    travel_times = {
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Nob Hill"): 7,

        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Nob Hill"): 8,

        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Mission District"): 18,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Nob Hill"): 8,

        ("Union Square", "North Beach"): 10,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Nob Hill"): 9,

        ("Mission District", "North Beach"): 17,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Nob Hill"): 12,

        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Nob Hill"): 20,

        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Golden Gate Park"): 17
    }

    # Friends: each friend is available at a specific location during a time window
    # Times are represented in minutes from midnight. For example, 9:00 AM = 540.
    friends = [
        {"name": "James",   "location": "Pacific Heights", "avail_start": 1200, "avail_end": 1320, "min_duration": 120},
        {"name": "Robert",  "location": "Chinatown",       "avail_start": 735,  "avail_end": 1005, "min_duration": 90},
        {"name": "Jeffrey", "location": "Union Square",    "avail_start": 570,  "avail_end": 930,  "min_duration": 120},
        {"name": "Carol",   "location": "Mission District","avail_start": 1095, "avail_end": 1275, "min_duration": 15},
        {"name": "Mark",    "location": "Golden Gate Park","avail_start": 690,  "avail_end": 1065, "min_duration": 15},
        {"name": "Sandra",  "location": "Nob Hill",        "avail_start": 480,  "avail_end": 930,  "min_duration": 15}
    ]
    n = len(friends)

    # Create an Optimize object
    opt = Optimize()

    # Decision variables:
    # meet[i]: if friend i is scheduled to meet (boolean)
    # s_vars[i]: start time of meeting with friend i (in minutes)
    # e_vars[i]: end time of meeting with friend i (in minutes)
    # order[i]: position of friend i in the itinerary if scheduled; unscheduled meetings get order -1.
    meet = [Bool(f"meet_{i}") for i in range(n)]
    s_vars = [Int(f"s_{i}") for i in range(n)]
    e_vars = [Int(f"e_{i}") for i in range(n)]
    order = [Int(f"order_{i}") for i in range(n)]

    # total_meetings is the total number of scheduled meetings.
    total_meetings = Int("total_meetings")
    opt.add(total_meetings == Sum([If(meet[i], 1, 0) for i in range(n)]))
    opt.add(total_meetings >= 0, total_meetings <= n)

    for i in range(n):
        friend = friends[i]
        # If a meeting is scheduled, the meeting must:
        # - Occur within the friend's availability window.
        # - Last at least the required duration.
        # - Be assigned a valid order (between 0 and n-1) and less than total_meetings.
        opt.add(Implies(meet[i],
                        And(
                            s_vars[i] >= friend["avail_start"],
                            e_vars[i] <= friend["avail_end"],
                            e_vars[i] - s_vars[i] >= friend["min_duration"],
                            order[i] >= 0,
                            order[i] < n,
                            order[i] < total_meetings,
                            s_vars[i] >= 0
                        )))
        # If not scheduled then set order to -1.
        opt.add(Implies(Not(meet[i]), order[i] == -1))

    # Ensure that scheduled meetings receive distinct order values.
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(meet[i], meet[j]), order[i] != order[j]))

    # For any scheduled meeting with order > 0, ensure that there is a preceding meeting with order exactly one less.
    for i in range(n):
        preceding_exists = []
        for j in range(n):
            if i != j:
                preceding_exists.append(And(meet[j], order[j] == order[i] - 1))
        if preceding_exists:
            opt.add(Implies(And(meet[i], order[i] > 0), Or(preceding_exists)))

    # Travel constraints:
    # For the meeting that is first in the itinerary, account for travel from "North Beach" (starting point at 9:00 AM, which is 540).
    for i in range(n):
        loc = friends[i]["location"]
        travel_from_start = travel_times.get(("North Beach", loc), 0)
        opt.add(Implies(And(meet[i], order[i] == 0),
                        s_vars[i] >= 540 + travel_from_start))

    # For consecutive meetings, ensure that the start time of the later meeting is at least
    # the end time of the earlier meeting plus the travel time between locations.
    for i in range(n):
        for j in range(n):
            if i != j:
                tt = travel_times.get((friends[i]["location"], friends[j]["location"]), 0)
                opt.add(Implies(And(meet[i], meet[j], order[j] == order[i] + 1),
                                s_vars[j] >= e_vars[i] + tt))

    # Objective: maximize number of meetings scheduled.
    opt.maximize(total_meetings)

    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for i in range(n):
            if is_true(model.evaluate(meet[i])):
                scheduled.append({
                    "name": friends[i]["name"],
                    "location": friends[i]["location"],
                    "start": model.evaluate(s_vars[i]).as_long(),
                    "end": model.evaluate(e_vars[i]).as_long(),
                    "order": model.evaluate(order[i]).as_long()
                })
        # Sort scheduled meetings by their order in the itinerary.
        scheduled.sort(key=lambda x: x["order"])
        itinerary = []
        for event in scheduled:
            itinerary.append({
                "action": "meet",
                "location": event["location"],
                "person": event["name"],
                "start_time": format_time(event["start"]),
                "end_time": format_time(event["end"])
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        # No valid itinerary found.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()