#!/usr/bin/env python3
import json
from z3 import *

def minutes_to_time(m):
    total = 9 * 60 + m
    hour = total // 60
    minute = total % 60
    return f"{hour}:{minute:02d}"

def main():
    friends = {
        1: ("Sarah", "Sunset District", 105, 600, 30),
        2: ("Richard", "Haight-Ashbury", 165, 405, 90),
        3: ("Elizabeth", "Mission District", 120, 495, 120),
        4: ("Michelle", "Golden Gate Park", 555, 705, 90)
    }

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
    
    unique_locations = { loc for (_, loc, _, _, _) in friends.values() }
    for loc in unique_locations:
        travel[(loc, loc)] = 0

    num_slots = 4
    opt = Optimize()

    friend_slots = [Int(f"friend_{i}") for i in range(num_slots)]
    start_times = [Int(f"start_{i}") for i in range(num_slots)]
    end_times   = [Int(f"end_{i}") for i in range(num_slots)]

    for i in range(num_slots):
        opt.add(Or(friend_slots[i] == 0, friend_slots[i] == 1, friend_slots[i] == 2, 
                   friend_slots[i] == 3, friend_slots[i] == 4))
        opt.add(Implies(friend_slots[i] == 0, And(start_times[i] == 0, end_times[i] == 0)))
        opt.add(Implies(friend_slots[i] != 0, start_times[i] > 0))
        opt.add(start_times[i] >= 0, end_times[i] >= 0)

    for i in range(num_slots - 1):
        opt.add(Implies(friend_slots[i] == 0, friend_slots[i+1] == 0))

    for i in range(num_slots):
        for j in range(i+1, num_slots):
            opt.add(Or(friend_slots[i] == 0, friend_slots[j] == 0, friend_slots[i] != friend_slots[j]))

    for i in range(num_slots):
        f_var = friend_slots[i]
        st = start_times[i]
        et = end_times[i]
        constraints = []
        for f_id, (name, location, avail_start, avail_end, min_dur) in friends.items():
            constraints.append(Implies(f_var == f_id, And(st >= avail_start, et <= avail_end, et - st >= min_dur)))
        opt.add(And(constraints))

    for i in range(num_slots - 1):
        for f in friends.keys():
            for g in friends.keys():
                opt.add(Implies(And(friend_slots[i] == f, friend_slots[i+1] == g),
                                end_times[i] + travel[(friends[f][1], friends[g][1])] <= start_times[i+1]))

    for f in friends.keys():
        opt.add(Implies(friend_slots[0] == f, start_times[0] >= travel[("Richmond District", friends[f][1])]))

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