import json
from z3 import *

def minutes_to_time(m):
    # m is minutes offset from 9:00
    total = 9 * 60 + m
    hour = total // 60
    minute = total % 60
    return f"{hour}:{minute:02d}"

def main():
    # Friend data: id -> (name, location, available_start, available_end, min_meeting_duration)
    # Times are in minutes offset from 9:00.
    # Sarah: 10:45 (105) to 19:00 (600), min 30 minutes.
    # Richard: 11:45 (165) to 15:45 (405), min 90 minutes.
    # Elizabeth: 11:00 (120) to 17:15 (495), min 120 minutes.
    # Michelle: 18:15 (555) to 20:45 (705), min 90 minutes.
    friends = {
        1: ("Sarah", "Sunset District", 105, 600, 30),
        2: ("Richard", "Haight-Ashbury", 165, 405, 90),
        3: ("Elizabeth", "Mission District", 120, 495, 120),
        4: ("Michelle", "Golden Gate Park", 555, 705, 90)
    }

    # Travel times (in minutes)
    travel = {
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Mission District"): 24,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Golden Gate Park"): 17,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Mission District"): 17
    }

    # We have up to 4 meeting slots (each slot is optionally assigned one friend).
    num_slots = 4
    opt = Optimize()

    # For each slot, we have:
    #   friend_i: integer variable in {0, 1,2,3,4} with 0 representing the slot is unused.
    #   start_i, end_i: meeting start and end (minutes offset from 9:00).
    friend_slots = [Int(f"friend_{i}") for i in range(num_slots)]
    start_times = [Int(f"start_{i}") for i in range(num_slots)]
    end_times   = [Int(f"end_{i}") for i in range(num_slots)]

    # Domain constraints for each slot.
    for i in range(num_slots):
        # friend variable is either 0 (unused) or one of 1,2,3,4.
        opt.add(Or(friend_slots[i] == 0, friend_slots[i] == 1, friend_slots[i] == 2, 
                   friend_slots[i] == 3, friend_slots[i] == 4))
        # If slot is unused, force its times to 0.
        opt.add(Implies(friend_slots[i] == 0, And(start_times[i] == 0, end_times[i] == 0)))
        # If slot is used, meeting must start after 9:00.
        opt.add(Implies(friend_slots[i] != 0, start_times[i] > 0))
        # Time variables non-negative.
        opt.add(start_times[i] >= 0, end_times[i] >= 0)

    # Enforce that meeting slots are consecutive; if a slot is empty, subsequent slots must be empty.
    for i in range(num_slots - 1):
        opt.add(Implies(friend_slots[i] == 0, friend_slots[i+1] == 0))

    # Uniqueness constraint: each friend may be scheduled at most once.
    for i in range(num_slots):
        for j in range(i+1, num_slots):
            opt.add(Or(friend_slots[i] == 0, friend_slots[j] == 0, friend_slots[i] != friend_slots[j]))

    # For each slot, if it is used then meeting time must lie within the friend's availability window 
    # and last at least the minimum required duration.
    for i in range(num_slots):
        f_var = friend_slots[i]
        st = start_times[i]
        et = end_times[i]
        constraints = []
        for f_id, (name, location, avail_start, avail_end, min_dur) in friends.items():
            constraints.append(Implies(f_var == f_id, And(st >= avail_start, et <= avail_end, et - st >= min_dur)))
        opt.add(And(constraints))

    # Travel constraints between consecutive filled slots.
    # If slot i is assigned friend f and slot i+1 is assigned friend g,
    # then meeting in slot i must finish and you must travel from friend f's location to friend g's location.
    for i in range(num_slots - 1):
        for f in friends.keys():
            for g in friends.keys():
                opt.add(Implies(And(friend_slots[i] == f, friend_slots[i+1] == g),
                                end_times[i] + travel[(friends[f][1], friends[g][1])] <= start_times[i+1]))

    # Constraint for the first meeting: travel from Richmond District to the meeting's location.
    for f in friends.keys():
        opt.add(Implies(friend_slots[0] == f, start_times[0] >= travel[("Richmond District", friends[f][1])]))

    # Objective: Maximize the number of meetings scheduled.
    meeting_count = Sum([If(friend_slots[i] != 0, 1, 0) for i in range(num_slots)])
    opt.maximize(meeting_count)

    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for i in range(num_slots):
            f_val = m.evaluate(friend_slots[i]).as_long()
            if f_val != 0:
                name, loc, avail_start, avail_end, min_dur = friends[f_val]
                s_time = m.evaluate(start_times[i]).as_long()
                e_time = m.evaluate(end_times[i]).as_long()
                itinerary.append({
                    "action": "meet",
                    "location": loc,
                    "person": name,
                    "start_time": minutes_to_time(s_time),
                    "end_time": minutes_to_time(e_time)
                })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()