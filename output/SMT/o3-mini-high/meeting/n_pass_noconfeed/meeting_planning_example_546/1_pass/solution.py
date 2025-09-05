from z3 import Optimize, Int, Bool, If, And, Or, Implies, sat, is_true
import json

def minutes_to_timestr(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    opt = Optimize()

    # Define friend data with availability (in minutes from midnight) and minimum meeting durations.
    # Kenneth: 21:15 - 22:00 (1275 to 1320), min 30
    # Lisa: 9:00 - 16:30 (540 to 990), min 45
    # Joshua: 12:00 - 15:15 (720 to 915), min 15
    # Nancy: 8:00 - 11:30 (480 to 690), min 90
    # Andrew: 11:30 - 20:15 (690 to 1215), min 60
    # John: 16:45 - 21:30 (1005 to 1290), min 75
    friends = [
        {"name": "Kenneth", "location": "Richmond District", "avail_start": 1275, "avail_end": 1320, "min_duration": 30},
        {"name": "Lisa",     "location": "Union Square",     "avail_start": 540,  "avail_end": 990,  "min_duration": 45},
        {"name": "Joshua",   "location": "Financial District", "avail_start": 720,  "avail_end": 915,  "min_duration": 15},
        {"name": "Nancy",    "location": "Pacific Heights",  "avail_start": 480,  "avail_end": 690,  "min_duration": 90},
        {"name": "Andrew",   "location": "Nob Hill",         "avail_start": 690,  "avail_end": 1215, "min_duration": 60},
        {"name": "John",     "location": "Bayview",          "avail_start": 1005, "avail_end": 1290, "min_duration": 75}
    ]

    # You arrive at Embarcadero at 9:00 AM (540 minutes)
    init_time = 540
    init_location = "Embarcadero"

    # Define travel times (in minutes) as given.
    travel_times = {
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Bayview"): 21,

        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Bayview"): 26,

        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Bayview"): 15,

        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Bayview"): 19,

        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Bayview"): 22,

        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Bayview"): 19,

        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Union Square"): 17,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Nob Hill"): 20,
    }

    n = len(friends)
    # Create decision variables:
    # meets[i] indicates if meeting with friend i is scheduled.
    # starts[i] is the start time of the meeting.
    # durations[i] is the meeting duration.
    meets = [Bool(f"meet_{i}") for i in range(n)]
    starts = [Int(f"s_{i}") for i in range(n)]
    durations = [Int(f"d_{i}") for i in range(n)]

    # Add constraints for each scheduled meeting.
    for i, friend in enumerate(friends):
        # Compute travel time from the starting location.
        travel_initial = travel_times[(init_location, friend["location"])]
        # If meeting is scheduled, then the meeting must start no earlier than the friend’s available start
        # and no earlier than your arrival at their location (init_time + travel time).
        opt.add(If(meets[i],
                   And(starts[i] >= friend["avail_start"],
                       starts[i] >= init_time + travel_initial),
                   True))
        # The meeting must finish before the friend's available end time.
        opt.add(If(meets[i],
                   starts[i] + durations[i] <= friend["avail_end"],
                   True))
        # The meeting duration must be at least the minimum required.
        opt.add(If(meets[i],
                   durations[i] >= friend["min_duration"],
                   True))
        # Basic non-negativity constraints.
        opt.add(starts[i] >= 0)
        opt.add(durations[i] >= 0)

    # Add non-overlap constraints with travel times between every pair of scheduled meetings.
    for i in range(n):
        for j in range(i + 1, n):
            travel_ij = travel_times[(friends[i]["location"], friends[j]["location"])]
            travel_ji = travel_times[(friends[j]["location"], friends[i]["location"])]
            # If both meetings are scheduled, then either i comes before j or j comes before i.
            opt.add(If(And(meets[i], meets[j]),
                       Or(starts[i] + durations[i] + travel_ij <= starts[j],
                          starts[j] + durations[j] + travel_ji <= starts[i]),
                       True))

    # Objective: maximize the number of friends you meet.
    meeting_count = sum([If(meet, 1, 0) for meet in meets])
    opt.maximize(meeting_count)

    # Check for a solution.
    if opt.check() == sat:
        model = opt.model()
        schedule = []
        for i, friend in enumerate(friends):
            if is_true(model.evaluate(meets[i])):
                s_val = model.evaluate(starts[i]).as_long()
                d_val = model.evaluate(durations[i]).as_long()
                e_val = s_val + d_val
                schedule.append((s_val, {
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_timestr(s_val),
                    "end_time": minutes_to_timestr(e_val)
                }))
        # Sort the meetings by start time.
        schedule.sort(key=lambda x: x[0])
        itinerary = [item[1] for item in schedule]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()