import json
from z3 import *

def convert_time(minutes_offset):
    # minutes_offset is minutes after 9:00
    total_minutes = 9 * 60 + minutes_offset
    hours = total_minutes // 60
    mins = total_minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Define travel times (in minutes) between locations
    travel_times = {
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "The Castro"): 19,

        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "The Castro"): 13,

        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "The Castro"): 16,

        ("Presidio", "Union Square"): 22,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "The Castro"): 21,

        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "The Castro"): 22,

        ("The Castro", "Union Square"): 19,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Chinatown"): 20,
    }

    # Define meeting constraints for each friend.
    # Times are represented as minutes after 9:00AM.
    # For each friend, we require the meeting to occur within their available time window.
    # Also, the meeting must start after you can reach the friend’s location from Union Square.
    # Note: For Robert, available from 8:30AM we adjust to 9:00AM start (i.e. 0 minutes offset).
    friends = [
        {
            "name": "Andrew",
            "location": "Golden Gate Park",
            "avail_start": 165,   # 11:45 AM (165 minutes after 9:00)
            "avail_end": 330,     # 14:30 (330 minutes after 9:00)
            "min_duration": 75,
            "start_from": travel_times[("Union Square", "Golden Gate Park")]
        },
        {
            "name": "Sarah",
            "location": "Pacific Heights",
            "avail_start": 435,   # 16:15
            "avail_end": 585,     # 18:45
            "min_duration": 15,
            "start_from": travel_times[("Union Square", "Pacific Heights")]
        },
        {
            "name": "Nancy",
            "location": "Presidio",
            "avail_start": 510,   # 17:30
            "avail_end": 615,     # 19:15
            "min_duration": 60,
            "start_from": travel_times[("Union Square", "Presidio")]
        },
        {
            "name": "Rebecca",
            "location": "Chinatown",
            "avail_start": 45,    # 9:45
            "avail_end": 750,     # 21:30
            "min_duration": 90,
            "start_from": travel_times[("Union Square", "Chinatown")]
        },
        {
            "name": "Robert",
            "location": "The Castro",
            "avail_start": 0,     # Start at 9:00 (even though available from 8:30)
            "avail_end": 315,     # 14:15
            "min_duration": 30,
            "start_from": travel_times[("Union Square", "The Castro")]
        }
    ]

    opt = Optimize()
    n = len(friends)

    # For each friend, create a meeting start time (minutes offset from 9:00) and a Boolean variable to indicate if the meeting is scheduled.
    meeting_starts = [Int(f"start_{i}") for i in range(n)]
    scheduled = [Bool(f"scheduled_{i}") for i in range(n)]

    # Add constraints for each scheduled meeting:
    for i, friend in enumerate(friends):
        # If scheduled, the meeting must start no earlier than the friend’s available start time.
        opt.add(Implies(scheduled[i], meeting_starts[i] >= friend["avail_start"]))
        # And you cannot arrive before you can get there from Union Square.
        opt.add(Implies(scheduled[i], meeting_starts[i] >= friend["start_from"]))
        # The meeting must finish by the available end time.
        opt.add(Implies(scheduled[i], meeting_starts[i] + friend["min_duration"] <= friend["avail_end"]))
        # Ensure meeting start is non-negative.
        opt.add(meeting_starts[i] >= 0)

    # Add pairwise separation constraints: if both meetings are scheduled they must be separated by travel time.
    for i in range(n):
        for j in range(i + 1, n):
            # For friend i and j, define finish times when scheduled.
            finish_i = meeting_starts[i] + friends[i]["min_duration"]
            finish_j = meeting_starts[j] + friends[j]["min_duration"]
            travel_ij = travel_times[(friends[i]["location"], friends[j]["location"])]
            travel_ji = travel_times[(friends[j]["location"], friends[i]["location"])]
            # If both meetings are scheduled then either i happens before j or j happens before i.
            opt.add(Implies(And(scheduled[i], scheduled[j]),
                            Or(finish_i + travel_ij <= meeting_starts[j],
                               finish_j + travel_ji <= meeting_starts[i])))

    # Objective: maximize the number of friends met.
    total_meetings = Sum([If(scheduled[i], 1, 0) for i in range(n)])
    h1 = opt.maximize(total_meetings)

    # Check if a solution exists and then extract the model.
    if opt.check() == sat:
        model = opt.model()
        meetings = []
        for i, friend in enumerate(friends):
            if is_true(model[scheduled[i]]):
                start_val = model[meeting_starts[i]].as_long()
                end_val = start_val + friend["min_duration"]
                meetings.append({
                    "person": friend["name"],
                    "location": friend["location"],
                    "start": start_val,
                    "end": end_val
                })
        # Sort the meetings in chronological order based on start time.
        meetings.sort(key=lambda m: m["start"])
        itinerary = []
        for m in meetings:
            itinerary.append({
                "action": "meet",
                "location": m["location"],
                "person": m["person"],
                "start_time": convert_time(m["start"]),
                "end_time": convert_time(m["end"])
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()