from z3 import *
import json

def minutes_to_time(t):
    hour = t // 60
    minute = t % 60
    return f"{hour}:{minute:02d}"

def main():
    # Travel times in minutes between locations
    travel = {
        "Bayview": {
            "North Beach": 22,
            "Fisherman's Wharf": 25,
            "Haight-Ashbury": 19,
            "Nob Hill": 20,
            "Golden Gate Park": 22,
            "Union Square": 18,
            "Alamo Square": 16,
            "Presidio": 32,
            "Chinatown": 19,
            "Pacific Heights": 23
        },
        "North Beach": {
            "Bayview": 25,
            "Fisherman's Wharf": 5,
            "Haight-Ashbury": 18,
            "Nob Hill": 7,
            "Golden Gate Park": 22,
            "Union Square": 7,
            "Alamo Square": 16,
            "Presidio": 17,
            "Chinatown": 6,
            "Pacific Heights": 8
        },
        "Fisherman's Wharf": {
            "Bayview": 26,
            "North Beach": 6,
            "Haight-Ashbury": 22,
            "Nob Hill": 11,
            "Golden Gate Park": 25,
            "Union Square": 13,
            "Alamo Square": 21,
            "Presidio": 17,
            "Chinatown": 12,
            "Pacific Heights": 12
        },
        "Haight-Ashbury": {
            "Bayview": 18,
            "North Beach": 19,
            "Fisherman's Wharf": 23,
            "Nob Hill": 15,
            "Golden Gate Park": 7,
            "Union Square": 19,
            "Alamo Square": 5,
            "Presidio": 15,
            "Chinatown": 19,
            "Pacific Heights": 12
        },
        "Nob Hill": {
            "Bayview": 19,
            "North Beach": 8,
            "Fisherman's Wharf": 10,
            "Haight-Ashbury": 13,
            "Golden Gate Park": 17,
            "Union Square": 7,
            "Alamo Square": 11,
            "Presidio": 17,
            "Chinatown": 6,
            "Pacific Heights": 8
        },
        "Golden Gate Park": {
            "Bayview": 23,
            "North Beach": 23,
            "Fisherman's Wharf": 24,
            "Haight-Ashbury": 7,
            "Nob Hill": 20,
            "Union Square": 22,
            "Alamo Square": 9,
            "Presidio": 11,
            "Chinatown": 23,
            "Pacific Heights": 16
        },
        "Union Square": {
            "Bayview": 15,
            "North Beach": 10,
            "Fisherman's Wharf": 15,
            "Haight-Ashbury": 18,
            "Nob Hill": 9,
            "Golden Gate Park": 22,
            "Alamo Square": 15,
            "Presidio": 24,
            "Chinatown": 7,
            "Pacific Heights": 15
        },
        "Alamo Square": {
            "Bayview": 16,
            "North Beach": 15,
            "Fisherman's Wharf": 19,
            "Haight-Ashbury": 5,
            "Nob Hill": 11,
            "Golden Gate Park": 9,
            "Union Square": 14,
            "Presidio": 17,
            "Chinatown": 15,
            "Pacific Heights": 10
        },
        "Presidio": {
            "Bayview": 31,
            "North Beach": 18,
            "Fisherman's Wharf": 19,
            "Haight-Ashbury": 15,
            "Nob Hill": 18,
            "Golden Gate Park": 12,
            "Union Square": 22,
            "Alamo Square": 19,
            "Chinatown": 21,
            "Pacific Heights": 11
        },
        "Chinatown": {
            "Bayview": 20,
            "North Beach": 3,
            "Fisherman's Wharf": 8,
            "Haight-Ashbury": 19,
            "Nob Hill": 9,
            "Golden Gate Park": 23,
            "Union Square": 7,
            "Alamo Square": 17,
            "Presidio": 19,
            "Pacific Heights": 10
        },
        "Pacific Heights": {
            "Bayview": 22,
            "North Beach": 9,
            "Fisherman's Wharf": 13,
            "Haight-Ashbury": 11,
            "Nob Hill": 8,
            "Golden Gate Park": 15,
            "Union Square": 12,
            "Alamo Square": 10,
            "Presidio": 11,
            "Chinatown": 11
        }
    }

    # Friend meeting constraints:
    # Times are represented in minutes from midnight.
    friend_infos = {
        "Brian": {
            "location": "North Beach",
            "avail_start": 13 * 60,      # 13:00 -> 780 minutes
            "avail_end": 19 * 60,        # 19:00 -> 1140 minutes
            "min_dur": 90
        },
        "Richard": {
            "location": "Fisherman's Wharf",
            "avail_start": 11 * 60,      # 11:00 -> 660 minutes
            "avail_end": 12 * 60 + 45,   # 12:45 -> 765 minutes
            "min_dur": 60
        },
        "Ashley": {
            "location": "Haight-Ashbury",
            "avail_start": 15 * 60,      # 15:00 -> 900 minutes
            "avail_end": 20 * 60 + 30,   # 20:30 -> 1230 minutes
            "min_dur": 90
        },
        "Elizabeth": {
            "location": "Nob Hill",
            "avail_start": 11 * 60 + 45, # 11:45 -> 705 minutes
            "avail_end": 18 * 60 + 30,   # 18:30 -> 1110 minutes
            "min_dur": 75
        },
        "Jessica": {
            "location": "Golden Gate Park",
            "avail_start": 20 * 60,      # 20:00 -> 1200 minutes
            "avail_end": 21 * 60 + 45,   # 21:45 -> 1305 minutes
            "min_dur": 105
        },
        "Deborah": {
            "location": "Union Square",
            "avail_start": 17 * 60 + 30, # 17:30 -> 1050 minutes
            "avail_end": 22 * 60,        # 22:00 -> 1320 minutes
            "min_dur": 60
        },
        "Kimberly": {
            "location": "Alamo Square",
            "avail_start": 17 * 60 + 30, # 17:30 -> 1050 minutes
            "avail_end": 21 * 60 + 15,   # 21:15 -> 1275 minutes
            "min_dur": 45
        },
        "Matthew": {
            "location": "Presidio",
            "avail_start": 8 * 60 + 15,  # 8:15 -> 495 minutes
            "avail_end": 9 * 60,         # 9:00 -> 540 minutes
            "min_dur": 15
        },
        "Kenneth": {
            "location": "Chinatown",
            "avail_start": 13 * 60 + 45, # 13:45 -> 825 minutes
            "avail_end": 19 * 60 + 30,   # 19:30 -> 1170 minutes
            "min_dur": 105
        },
        "Anthony": {
            "location": "Pacific Heights",
            "avail_start": 14 * 60 + 15, # 14:15 -> 855 minutes
            "avail_end": 16 * 60,        # 16:00 -> 960 minutes
            "min_dur": 30
        }
    }

    # List of friends (meeting candidates)
    meeting_names = list(friend_infos.keys())

    # Starting constraints: You arrive at Bayview at 9:00 (540 minutes)
    start_time = 9 * 60  # 540 minutes

    opt = Optimize()

    # Create decision variables for each meeting:
    s_vars = {}       # meeting start time
    e_vars = {}       # meeting end time
    scheduled = {}    # whether the meeting is scheduled

    for name in meeting_names:
        s_vars[name] = Int(f"s_{name}")
        e_vars[name] = Int(f"e_{name}")
        scheduled[name] = Bool(f"scheduled_{name}")
        # Constrain times to be in a valid window (0 to 1440 minutes)
        opt.add(s_vars[name] >= 0, s_vars[name] <= 1440)
        opt.add(e_vars[name] >= 0, e_vars[name] <= 1440)

        info = friend_infos[name]
        loc = info["location"]

        # If meeting is scheduled, it must occur within the friend's available time window.
        opt.add(Implies(scheduled[name], s_vars[name] >= info["avail_start"]))
        opt.add(Implies(scheduled[name], e_vars[name] <= info["avail_end"]))
        opt.add(Implies(scheduled[name], e_vars[name] - s_vars[name] >= info["min_dur"]))
        # Also, ensure you can reach the meeting from Bayview
        opt.add(Implies(scheduled[name], s_vars[name] >= start_time + travel["Bayview"][loc]))

    # Add disjunctive ordering constraints between any two scheduled meetings.
    # For any two meetings i and j, if both are scheduled, then one must occur after the other accounting for travel time.
    for i in range(len(meeting_names)):
        for j in range(i + 1, len(meeting_names)):
            name_i = meeting_names[i]
            name_j = meeting_names[j]
            loc_i = friend_infos[name_i]["location"]
            loc_j = friend_infos[name_j]["location"]
            travel_ji = travel[loc_j][loc_i]  # travel from meeting j to meeting i
            travel_ij = travel[loc_i][loc_j]  # travel from meeting i to meeting j

            opt.add(
                Implies(
                    And(scheduled[name_i], scheduled[name_j]),
                    Or(
                        s_vars[name_i] >= e_vars[name_j] + travel_ji,
                        s_vars[name_j] >= e_vars[name_i] + travel_ij
                    )
                )
            )

    # Objective: maximize the number of meetings scheduled.
    opt.maximize(Sum([If(scheduled[name], 1, 0) for name in meeting_names]))

    # Solve the optimization problem.
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for name in meeting_names:
            if is_true(model.evaluate(scheduled[name])):
                start_val = model.evaluate(s_vars[name]).as_long()
                end_val = model.evaluate(e_vars[name]).as_long()
                scheduled_meetings.append({
                    "person": name,
                    "location": friend_infos[name]["location"],
                    "start": start_val,
                    "end": end_val
                })
        # Sort scheduled meetings by their start time.
        scheduled_meetings.sort(key=lambda x: x["start"])

        itinerary = []
        for meet in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": meet["location"],
                "person": meet["person"],
                "start_time": minutes_to_time(meet["start"]),
                "end_time": minutes_to_time(meet["end"])
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()