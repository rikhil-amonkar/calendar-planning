from z3 import *
import json

def format_time(t):
    # Format minutes since midnight as H:MM (24-hour, no leading zero for hour).
    hour = t // 60
    minute = t % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times (in minutes) between locations.
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
        ("Nob Hill", "Golden Gate Park"): 17,
    }

    # Define meeting events.
    # Times are in minutes from midnight.
    # Each event has: person, location, available start, available end, and minimum required meeting duration.
    events = [
        {
            "person": "James",
            "location": "Pacific Heights",
            "avail_start": 20 * 60,   # 20:00
            "avail_end": 22 * 60,     # 22:00
            "duration": 120
        },
        {
            "person": "Robert",
            "location": "Chinatown",
            "avail_start": 12 * 60 + 15,  # 12:15
            "avail_end": 16 * 60 + 45,    # 16:45
            "duration": 90
        },
        {
            "person": "Jeffrey",
            "location": "Union Square",
            "avail_start": 9 * 60 + 30,   # 9:30
            "avail_end": 15 * 60 + 30,    # 15:30
            "duration": 120
        },
        {
            "person": "Carol",
            "location": "Mission District",
            "avail_start": 18 * 60 + 15,  # 18:15
            "avail_end": 21 * 60 + 15,    # 21:15
            "duration": 15
        },
        {
            "person": "Mark",
            "location": "Golden Gate Park",
            "avail_start": 11 * 60 + 30,  # 11:30
            "avail_end": 17 * 60 + 45,    # 17:45
            "duration": 15
        },
        {
            "person": "Sandra",
            "location": "Nob Hill",
            "avail_start": 8 * 60,        # 8:00
            "avail_end": 15 * 60 + 30,     # 15:30
            "duration": 15
        },
    ]

    # You arrive at North Beach at 9:00 (540 minutes).
    START_TIME = 9 * 60

    # Create an Optimize instance.
    opt = Optimize()

    # For each event, create SMT variables:
    # S: start time of meeting (in minutes) if scheduled.
    # mvar: Boolean variable that indicates if the meeting is scheduled.
    for i, ev in enumerate(events):
        s = Int(f"S_{i}")
        mvar = Bool(f"meet_{i}")
        ev["S"] = s
        ev["mvar"] = mvar

        # If the meeting is scheduled, its start time must be within the available window.
        opt.add(Implies(mvar, s >= ev["avail_start"]))
        opt.add(Implies(mvar, s <= ev["avail_end"] - ev["duration"]))

        # Special constraint for James: if scheduled, he must be met starting exactly at 20:00.
        if ev["person"] == "James":
            opt.add(Implies(mvar, s == 20 * 60))

        # For Carol and James: if both are scheduled, Carol must finish early enough to travel to Pacific Heights by 20:00.
        if ev["person"] == "Carol":
            # Find the James event index.
            james_index = None
            for j, ev2 in enumerate(events):
                if ev2["person"] == "James":
                    james_index = j
                    break
            if james_index is not None:
                # Travel time from Mission District (Carol's location) to Pacific Heights.
                travel_c_to_p = travel_times[(ev["location"], "Pacific Heights")]
                # If both Carol and James are scheduled, then:
                # Carol's finish time plus travel must be <= 20:00.
                opt.add(Implies(And(mvar, events[james_index]["mvar"]),
                                s + ev["duration"] + travel_c_to_p <= 20 * 60))

        # Regardless of ordering, if a meeting is scheduled, you must be able to get there directly
        # from your start location (North Beach at 9:00).
        travel_from_start = travel_times[("North Beach", ev["location"])]
        opt.add(Implies(mvar, s >= START_TIME + travel_from_start))

    n = len(events)
    # For every pair of meetings, if both are scheduled they must not overlap.
    # This is enforced by requiring that one meeting finishes, plus travel time to the other meeting's location, before the other meeting starts.
    for i in range(n):
        for j in range(i + 1, n):
            ev_i = events[i]
            ev_j = events[j]
            # Travel time from event i's location to event j's location.
            t_ij = travel_times[(ev_i["location"], ev_j["location"])]
            t_ji = travel_times[(ev_j["location"], ev_i["location"])]
            opt.add(Implies(And(ev_i["mvar"], ev_j["mvar"]),
                            Or(ev_i["S"] + ev_i["duration"] + t_ij <= ev_j["S"],
                               ev_j["S"] + ev_j["duration"] + t_ji <= ev_i["S"])))
    
    # Objective: maximize the number of meetings scheduled.
    total_meetings = Sum([If(ev["mvar"], 1, 0) for ev in events])
    opt.maximize(total_meetings)

    # Solve the scheduling problem.
    if opt.check() == sat:
        model = opt.model()
        scheduled_events = []
        for ev in events:
            if is_true(model.evaluate(ev["mvar"])):
                start = model.evaluate(ev["S"]).as_long()
                end = start + ev["duration"]
                scheduled_events.append((start, {
                    "action": "meet",
                    "location": ev["location"],
                    "person": ev["person"],
                    "start_time": format_time(start),
                    "end_time": format_time(end)
                }))
        # Sort the scheduled meetings by start time.
        scheduled_events.sort(key=lambda x: x[0])
        itinerary = [item[1] for item in scheduled_events]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()