from z3 import *
import json

def minutes_to_time_str(m):
    h = m // 60
    mins = m % 60
    return f"{h}:{mins:02d}"

def main():
    # Define friend availability and meeting requirements.
    # Times are in minutes from midnight.
    # 9:00 AM = 540, etc.
    friends = [
        {"person": "Carol",    "location": "Haight-Ashbury",    "avail_start": 21*60+30, "avail_end": 22*60+30, "min_duration": 60},   # 21:30 to 22:30
        {"person": "Laura",    "location": "Fisherman's Wharf", "avail_start": 11*60+45, "avail_end": 21*60+30, "min_duration": 60},   # 11:45 to 21:30
        {"person": "Karen",    "location": "The Castro",        "avail_start": 7*60+15,  "avail_end": 14*60,    "min_duration": 75},   # 7:15 to 14:00
        {"person": "Elizabeth","location": "Chinatown",         "avail_start": 12*60+15, "avail_end": 21*60+30, "min_duration": 75},   # 12:15 to 21:30
        {"person": "Deborah",  "location": "Alamo Square",      "avail_start": 12*60,    "avail_end": 15*60,    "min_duration": 105},  # 12:00 to 15:00
        {"person": "Jason",    "location": "North Beach",       "avail_start": 14*60+45, "avail_end": 19*60,    "min_duration": 90},   # 14:45 to 19:00
        {"person": "Steven",   "location": "Russian Hill",      "avail_start": 14*60+45, "avail_end": 18*60+30, "min_duration": 120}   # 14:45 to 18:30
    ]
    n_friends = len(friends)
    max_slots = n_friends  # Maximum number of meetings we could schedule

    # Starting position: Golden Gate Park at 9:00 (540 minutes)
    # Travel times from Golden Gate Park to each friend's location:
    # Golden Gate Park -> Haight-Ashbury, Fisherman's Wharf, The Castro, Chinatown,
    # Alamo Square, North Beach, Russian Hill.
    start_travel = [7, 24, 13, 23, 10, 24, 19]

    # Travel time matrix between meeting locations (in minutes)
    # Order of friends: 0:Carol (Haight-Ashbury), 
    # 1:Laura (Fisherman's Wharf), 2:Karen (The Castro),
    # 3:Elizabeth (Chinatown), 4:Deborah (Alamo Square),
    # 5:Jason (North Beach), 6:Steven (Russian Hill).
    travel = [
        # To:    0      1      2      3      4      5      6
        [   0,    23,     6,    19,     5,    19,    17],  # From Carol (Haight-Ashbury)
        [  22,     0,    26,    12,    20,     6,     7],  # From Laura (Fisherman's Wharf)
        [   6,    24,     0,    20,     8,    20,    18],  # From Karen (The Castro)
        [  19,     8,    22,     0,    17,     3,     7],  # From Elizabeth (Chinatown)
        [   5,    19,     8,    16,     0,    15,    13],  # From Deborah (Alamo Square)
        [  18,     5,    22,     6,    16,     0,     4],  # From Jason (North Beach)
        [  17,     7,    21,     9,    15,     5,     0]   # From Steven (Russian Hill)
    ]

    # Create an Optimize object from Z3 to maximize meetings scheduled.
    opt = Optimize()

    # Decision variables.
    # slots[i]: integer variable representing the friend assigned to slot i.
    # A value of -1 indicates that the slot is unused.
    slots = [Int(f"slot_{i}") for i in range(max_slots)]
    # S[i]: start time (in minutes) of the meeting in slot i.
    S = [Int(f"S_{i}") for i in range(max_slots)]

    # Domain constraints for each slot and meeting start time.
    for i in range(max_slots):
        # Either slot is unused (-1) or holds a valid friend index [0, n_friends-1].
        opt.add(Or(slots[i] == -1, And(slots[i] >= 0, slots[i] < n_friends)))
        # Bound meeting start times between 0 and 1440 (midnight)
        opt.add(S[i] >= 0, S[i] <= 1440)

    # Ensure that once a slot is unused, all later slots remain unused.
    for i in range(1, max_slots):
        opt.add(Or(slots[i] == -1, slots[i-1] != -1))

    # No friend is scheduled twice.
    for i in range(max_slots):
        for j in range(i + 1, max_slots):
            opt.add(Or(slots[i] == -1, slots[j] == -1, slots[i] != slots[j]))

    # For each slot, if a friend is scheduled there then the meeting must
    # respect that friend's availability window and minimum meeting duration.
    for i in range(max_slots):
        for k in range(n_friends):
            d = friends[k]["min_duration"]
            astart = friends[k]["avail_start"]
            aend = friends[k]["avail_end"]
            # If friend k is in slot i then S[i] must be no earlier than the friend's available start...
            opt.add(Implies(slots[i] == k, S[i] >= astart))
            # ...and the meeting must finish by the available end.
            opt.add(Implies(slots[i] == k, S[i] + d <= aend))

    # Travel constraints between meetings.
    # For the first meeting: account for travel time from Golden Gate Park.
    for k in range(n_friends):
        opt.add(Implies(slots[0] == k, S[0] >= 540 + start_travel[k]))
    # For subsequent meetings, ensure travel time between the meeting locations.
    for i in range(1, max_slots):
        for j in range(n_friends):
            for k in range(n_friends):
                d_prev = friends[j]["min_duration"]
                tt = travel[j][k]  # travel time from location of friend j to friend k
                opt.add(Implies(And(slots[i-1] == j, slots[i] == k), S[i] >= S[i-1] + d_prev + tt))

    # Define objective: maximize the number of meetings scheduled.
    num_meetings = Sum([If(slots[i] != -1, 1, 0) for i in range(max_slots)])
    opt.maximize(num_meetings)

    # Solve the optimization problem.
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        # Only include slots that are used (contiguous from slot 0 up).
        for i in range(max_slots):
            slot_val = model.evaluate(slots[i]).as_long()
            if slot_val != -1:
                start_time = model.evaluate(S[i]).as_long()
                duration = friends[slot_val]["min_duration"]
                meeting = {
                    "action": "meet",
                    "location": friends[slot_val]["location"],
                    "person": friends[slot_val]["person"],
                    "start_time": minutes_to_time_str(start_time),
                    "end_time": minutes_to_time_str(start_time + duration)
                }
                itinerary.append(meeting)
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()