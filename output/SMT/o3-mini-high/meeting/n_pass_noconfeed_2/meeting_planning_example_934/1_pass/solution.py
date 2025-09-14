from z3 import *
import json

def minutes_to_time(m):
    # Convert minutes (from midnight) to "H:MM" 24-hour format (no leading zeros on hour)
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

def main():
    # Travel times in minutes between locations (directed)
    travel = {
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Russian Hill"): 5,

        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Russian Hill"): 8,

        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Russian Hill"): 18,

        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Russian Hill"): 17,

        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Russian Hill"): 13,

        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Russian Hill"): 4,

        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Russian Hill"): 7,

        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Russian Hill"): 7,

        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Russian Hill"): 19,

        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Russian Hill"): 8,

        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Marina District"): 7
    }

    # Meeting constraints and details for each friend
    # Times are in minutes from midnight (e.g., 9:00AM is 540)
    meetings_data = [
        {"person": "Mary",    "location": "Embarcadero",      "avail_start": 1200, "avail_end": 1275, "min_duration": 75},
        {"person": "Kenneth", "location": "The Castro",       "avail_start": 675,  "avail_end": 1155, "min_duration": 30},
        {"person": "Joseph",  "location": "Haight-Ashbury",   "avail_start": 1200, "avail_end": 1320, "min_duration": 120},
        {"person": "Sarah",   "location": "Union Square",     "avail_start": 705,  "avail_end": 870,  "min_duration": 90},
        {"person": "Thomas",  "location": "North Beach",      "avail_start": 1155, "avail_end": 1185, "min_duration": 15},
        {"person": "Daniel",  "location": "Pacific Heights",  "avail_start": 825,  "avail_end": 1230, "min_duration": 15},
        {"person": "Richard", "location": "Chinatown",        "avail_start": 480,  "avail_end": 1125, "min_duration": 30},
        {"person": "Mark",    "location": "Golden Gate Park", "avail_start": 1050, "avail_end": 1290, "min_duration": 120},
        {"person": "David",   "location": "Marina District",  "avail_start": 1200, "avail_end": 1260, "min_duration": 60},
        {"person": "Karen",   "location": "Russian Hill",     "avail_start": 795,  "avail_end": 1110, "min_duration": 120},
    ]

    # Create a Z3 Optimize() solver instance.
    opt = Optimize()

    # Create Z3 variables for each meeting.
    meetings = []
    for m in meetings_data:
        meeting = m.copy()
        person = m["person"]
        meeting["x"] = Bool("x_" + person)  # Whether to schedule this meeting
        meeting["s"] = Int("s_" + person)     # Start time of meeting (in minutes)
        meeting["e"] = Int("e_" + person)     # End time of meeting (in minutes)
        meetings.append(meeting)
        # Basic domain constraint for start times.
        opt.add(meeting["s"] >= 0)
        # If the meeting is scheduled, it must occur within the friend's availability window
        opt.add(Implies(meeting["x"], meeting["s"] >= meeting["avail_start"]))
        opt.add(Implies(meeting["x"], meeting["s"] >= 540 + travel[("Nob Hill", meeting["location"])]))
        opt.add(Implies(meeting["x"], meeting["s"] + meeting["min_duration"] <= meeting["avail_end"]))
        opt.add(Implies(meeting["x"], meeting["e"] == meeting["s"] + meeting["min_duration"]))

    # Add ordering (non-overlap with travel) constraints between every pair of scheduled meetings.
    n = len(meetings)
    for i in range(n):
        for j in range(i + 1, n):
            a = meetings[i]
            b = meetings[j]
            # If both meetings are scheduled, then either a comes before b or vice versa.
            opt.add(
                Implies(And(a["x"], b["x"]),
                    Or(
                        And(a["s"] <= b["s"], b["s"] >= a["e"] + travel[(a["location"], b["location"])]),
                        And(b["s"] < a["s"], a["s"] >= b["e"] + travel[(b["location"], a["location"])])
                    )
                )
            )

    # Objective: maximize the number of meetings scheduled.
    total_meetings = Sum([If(m["x"], 1, 0) for m in meetings])
    opt.maximize(total_meetings)

    # Check for a solution.
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for m in meetings:
            if is_true(model.evaluate(m["x"])):
                s_val = model.evaluate(m["s"]).as_long()
                e_val = model.evaluate(m["e"]).as_long()
                scheduled.append({
                    "person": m["person"],
                    "location": m["location"],
                    "s": s_val,
                    "e": e_val
                })
        # Sort the meetings by start time.
        scheduled.sort(key=lambda m: m["s"])
        itinerary = []
        for m in scheduled:
            itinerary.append({
                "action": "meet",
                "location": m["location"],
                "person": m["person"],
                "start_time": minutes_to_time(m["s"]),
                "end_time": minutes_to_time(m["e"])
            })
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()