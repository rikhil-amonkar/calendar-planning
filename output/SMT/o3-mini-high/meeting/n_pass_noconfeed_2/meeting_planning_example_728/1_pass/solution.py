from z3 import Optimize, Int, Bool, If, Or, And, Sum, sat
import json

def minutes_to_time(m):
    # m is minutes since 9:00 AM; add 9*60 to get minutes from midnight.
    total = m + 9 * 60
    hour = total // 60
    minute = total % 60
    return f"{hour}:{minute:02d}"

def main():
    # Travel times in minutes (non-symmetric)
    travel = {
        "Marina District": {
            "Mission District": 20,
            "Fisherman's Wharf": 10,
            "Presidio": 10,
            "Union Square": 16,
            "Sunset District": 19,
            "Financial District": 17,
            "Haight-Ashbury": 16,
            "Russian Hill": 8
        },
        "Mission District": {
            "Marina District": 19,
            "Fisherman's Wharf": 22,
            "Presidio": 25,
            "Union Square": 15,
            "Sunset District": 24,
            "Financial District": 15,
            "Haight-Ashbury": 12,
            "Russian Hill": 15
        },
        "Fisherman's Wharf": {
            "Marina District": 9,
            "Mission District": 22,
            "Presidio": 17,
            "Union Square": 13,
            "Sunset District": 27,
            "Financial District": 11,
            "Haight-Ashbury": 22,
            "Russian Hill": 7
        },
        "Presidio": {
            "Marina District": 11,
            "Mission District": 26,
            "Fisherman's Wharf": 19,
            "Union Square": 22,
            "Sunset District": 16,
            "Financial District": 23,
            "Haight-Ashbury": 15,
            "Russian Hill": 14
        },
        "Union Square": {
            "Marina District": 18,
            "Mission District": 14,
            "Fisherman's Wharf": 15,
            "Presidio": 24,
            "Sunset District": 27,
            "Financial District": 9,
            "Haight-Ashbury": 18,
            "Russian Hill": 13
        },
        "Sunset District": {
            "Marina District": 21,
            "Mission District": 25,
            "Fisherman's Wharf": 29,
            "Presidio": 16,
            "Union Square": 30,
            "Financial District": 30,
            "Haight-Ashbury": 15,
            "Russian Hill": 24
        },
        "Financial District": {
            "Marina District": 15,
            "Mission District": 17,
            "Fisherman's Wharf": 10,
            "Presidio": 22,
            "Union Square": 9,
            "Sunset District": 30,
            "Haight-Ashbury": 19,
            "Russian Hill": 11
        },
        "Haight-Ashbury": {
            "Marina District": 17,
            "Mission District": 11,
            "Fisherman's Wharf": 23,
            "Presidio": 15,
            "Union Square": 19,
            "Sunset District": 15,
            "Financial District": 21,
            "Russian Hill": 17
        },
        "Russian Hill": {
            "Marina District": 7,
            "Mission District": 16,
            "Fisherman's Wharf": 7,
            "Presidio": 14,
            "Union Square": 10,
            "Sunset District": 23,
            "Financial District": 11,
            "Haight-Ashbury": 17
        }
    }

    # Friend meeting constraints with time windows given in minutes from 9:00 AM.
    # For example, 2:15PM is 14:15, which is 315 minutes after 9:00.
    friends = [
        {"name": "Karen", "location": "Mission District", "avail_start": 315, "avail_end": 780, "min_duration": 30},
        {"name": "Richard", "location": "Fisherman's Wharf", "avail_start": 330, "avail_end": 510, "min_duration": 30},
        {"name": "Robert", "location": "Presidio", "avail_start": 765, "avail_end": 825, "min_duration": 60},
        {"name": "Joseph", "location": "Union Square", "avail_start": 165, "avail_end": 345, "min_duration": 120},
        {"name": "Helen", "location": "Sunset District", "avail_start": 345, "avail_end": 705, "min_duration": 105},
        {"name": "Elizabeth", "location": "Financial District", "avail_start": 60, "avail_end": 225, "min_duration": 75},
        {"name": "Kimberly", "location": "Haight-Ashbury", "avail_start": 315, "avail_end": 510, "min_duration": 105},
        {"name": "Ashley", "location": "Russian Hill", "avail_start": 150, "avail_end": 750, "min_duration": 45},
    ]

    opt = Optimize()
    n = len(friends)

    # Create variables for each meeting:
    # attend[i]: Boolean whether to meet friend i.
    # s[i]: start time (minutes from 9:00) of meeting i.
    # e[i]: end time of meeting i.
    attend = [Bool(f"attend_{i}") for i in range(n)]
    s = [Int(f"s_{i}") for i in range(n)]
    e = [Int(f"e_{i}") for i in range(n)]

    # Each meeting has to be scheduled within the friend’s available time window if attended,
    # with a minimum meeting duration, and if it is held its start must respect the travel time from Marina.
    for i, friend in enumerate(friends):
        opt.add(
            If(
                attend[i],
                And(
                    s[i] >= friend["avail_start"],
                    e[i] <= friend["avail_end"],
                    e[i] - s[i] >= friend["min_duration"],
                    s[i] >= travel["Marina District"][friend["location"]]
                ),
                And(s[i] == 0, e[i] == 0)
            )
        )

    # For every pair of meetings, if both are attended then they must not overlap.
    # That is, one meeting must finish (plus travel time from its location to the next)
    # before the other begins.
    for i in range(n):
        for j in range(i + 1, n):
            loc_i = friends[i]["location"]
            loc_j = friends[j]["location"]
            opt.add(
                # Only enforce the constraint if both meetings are attended.
                # Either meeting i then j, or meeting j then i must hold.
                If(
                    And(attend[i], attend[j]),
                    Or(
                        e[i] + travel[loc_i][loc_j] <= s[j],
                        e[j] + travel[loc_j][loc_i] <= s[i]
                    ),
                    True
                )
            )

    # Maximize the number of meetings attended.
    opt.maximize(Sum([If(attend[i], 1, 0) for i in range(n)]))

    if opt.check() == sat:
        model = opt.model()
        meetings = []
        for i, friend in enumerate(friends):
            if model.evaluate(attend[i]):
                start_val = model.evaluate(s[i]).as_long()
                end_val = model.evaluate(e[i]).as_long()
                meetings.append((start_val, {
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                }))
        # Sort meetings by start time
        meetings.sort(key=lambda x: x[0])
        itinerary = [m[1] for m in meetings]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()