import json
from z3 import *

def minutes_to_str(t):
    # Convert integer minutes since midnight to "H:MM" 24-hour format.
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Arrival time at Bayview: 9:00 AM => 540 minutes.
    arrival_time = 540

    # Define each friend's meeting info.
    # Times are in minutes from midnight.
    friend_data = [
        {
            "name": "Paul",
            "location": "Nob Hill",
            "avail_start": 16 * 60 + 15,  # 16:15 -> 975
            "avail_end": 21 * 60 + 15,    # 21:15 -> 1275
            "min_duration": 60
        },
        {
            "name": "Carol",
            "location": "Union Square",
            "avail_start": 18 * 60,       # 18:00 -> 1080
            "avail_end": 20 * 60 + 15,    # 20:15 -> 1215
            "min_duration": 120
        },
        {
            "name": "Patricia",
            "location": "Chinatown",
            "avail_start": 20 * 60,       # 20:00 -> 1200
            "avail_end": 21 * 60 + 30,    # 21:30 -> 1290
            "min_duration": 75
        },
        {
            "name": "Karen",
            "location": "The Castro",
            "avail_start": 17 * 60,       # 17:00 -> 1020
            "avail_end": 19 * 60,         # 19:00 -> 1140
            "min_duration": 45
        },
        {
            "name": "Nancy",
            "location": "Presidio",
            "avail_start": 11 * 60 + 45,  # 11:45 -> 705
            "avail_end": 22 * 60,         # 22:00 -> 1320
            "min_duration": 30
        },
        {
            "name": "Jeffrey",
            "location": "Pacific Heights",
            "avail_start": 20 * 60,       # 20:00 -> 1200
            "avail_end": 20 * 60 + 45,    # 20:45 -> 1245
            "min_duration": 45
        },
        {
            "name": "Matthew",
            "location": "Russian Hill",
            "avail_start": 15 * 60 + 45,  # 15:45 -> 945
            "avail_end": 21 * 60 + 45,    # 21:45 -> 1305
            "min_duration": 75
        }
    ]

    # Travel times (in minutes) between locations.
    # The keys are tuples (from_location, to_location).
    travel = {
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Union Square"): 17,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "The Castro"): 20,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Russian Hill"): 23,

        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Russian Hill"): 5,

        ("Union Square", "Bayview"): 15,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "The Castro"): 19,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Russian Hill"): 13,

        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "Nob Hill"): 8,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Russian Hill"): 7,

        ("The Castro", "Bayview"): 19,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Chinatown"): 20,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Russian Hill"): 18,

        ("Presidio", "Bayview"): 31,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Russian Hill"): 14,

        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Russian Hill"): 7,

        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Union Square"): 11,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Pacific Heights"): 7,
    }

    num_friends = len(friend_data)

    # Create an optimization instance.
    opt = Optimize()

    # Decision variables.
    # x[i] is True if meeting with friend i is scheduled.
    x = [Bool(f"x_{i}") for i in range(num_friends)]
    # S[i] and E[i] are the start and end times (in minutes) of the meeting with friend i.
    S = [Int(f"S_{i}") for i in range(num_friends)]
    E = [Int(f"E_{i}") for i in range(num_friends)]

    # For each friend meeting i, if scheduled, then:
    #   - The meeting must start no earlier than the friend's availability window.
    #   - The meeting must start no earlier than the time it takes to go directly from Bayview.
    #   - The meeting must end by the end of the availability window.
    #   - The meeting must last at least the minimum required duration.
    for i in range(num_friends):
        info = friend_data[i]
        loc = info["location"]
        avail_start = info["avail_start"]
        avail_end = info["avail_end"]
        min_dur = info["min_duration"]

        opt.add(Implies(x[i], S[i] >= avail_start))
        opt.add(Implies(x[i], S[i] >= arrival_time + travel[("Bayview", loc)]))
        opt.add(Implies(x[i], E[i] <= avail_end))
        opt.add(Implies(x[i], E[i] - S[i] >= min_dur))

    # For each pair of meetings, if both are scheduled, enforce that one is scheduled after the other
    # with enough travel time between the locations.
    for i in range(num_friends):
        for j in range(i + 1, num_friends):
            loc_i = friend_data[i]["location"]
            loc_j = friend_data[j]["location"]
            travel_ij = travel[(loc_i, loc_j)]
            travel_ji = travel[(loc_j, loc_i)]
            opt.add(Implies(And(x[i], x[j]),
                            Or(E[i] + travel_ij <= S[j],
                               E[j] + travel_ji <= S[i])))

    # Objective: maximize the number of scheduled meetings.
    opt.maximize(Sum([If(x[i], 1, 0) for i in range(num_friends)]))

    # Check and obtain model.
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for i in range(num_friends):
            if model.evaluate(x[i]):
                start_val = model.evaluate(S[i]).as_long()
                end_val = model.evaluate(E[i]).as_long()
                scheduled.append((start_val, i, end_val))
        # Sort the scheduled meetings in chronological order.
        scheduled.sort(key=lambda tup: tup[0])

        itinerary = []
        for start_val, i, end_val in scheduled:
            itinerary.append({
                "action": "meet",
                "location": friend_data[i]["location"],
                "person": friend_data[i]["name"],
                "start_time": minutes_to_str(start_val),
                "end_time": minutes_to_str(end_val)
            })

        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()