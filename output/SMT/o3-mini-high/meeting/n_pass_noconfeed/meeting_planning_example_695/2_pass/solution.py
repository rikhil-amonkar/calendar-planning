#!/usr/bin/env python3
from z3 import *
import json

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    friends = [
        {"name": "Paul",    "location": "Nob Hill",        "avail_start": 975,  "avail_end": 1275, "min_duration": 60},
        {"name": "Carol",   "location": "Union Square",    "avail_start": 1080, "avail_end": 1215, "min_duration": 120},
        {"name": "Patricia","location": "Chinatown",       "avail_start": 1200, "avail_end": 1290, "min_duration": 75},
        {"name": "Karen",   "location": "The Castro",      "avail_start": 1020, "avail_end": 1140, "min_duration": 45},
        {"name": "Nancy",   "location": "Presidio",        "avail_start": 705,  "avail_end": 1320, "min_duration": 30},
        {"name": "Jeffrey", "location": "Pacific Heights", "avail_start": 1200, "avail_end": 1245, "min_duration": 45},
        {"name": "Matthew", "location": "Russian Hill",    "avail_start": 945,  "avail_end": 1305, "min_duration": 75}
    ]
    
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
        ("Russian Hill", "Pacific Heights"): 7
    }
    
    locations = {"Bayview", "Nob Hill", "Union Square", "Chinatown", "The Castro", "Presidio", "Pacific Heights", "Russian Hill"}
    for loc in locations:
        if (loc, loc) not in travel:
            travel[(loc, loc)] = 0
    
    n_slots = 7
    opt = Optimize()
    slots = [Int(f"slot_{i}") for i in range(n_slots)]
    s_times = [Int(f"s_{i}") for i in range(n_slots)]
    e_times = [Int(f"e_{i}") for i in range(n_slots)]
    
    for i in range(n_slots):
        opt.add(Or(slots[i] == -1, And(slots[i] >= 0, slots[i] < len(friends))))
    
    for i in range(n_slots):
        opt.add(Implies(slots[i] == -1, And(s_times[i] == 0, e_times[i] == 0)))
    
    for i in range(n_slots):
        for f in range(len(friends)):
            friend = friends[f]
            opt.add(Implies(slots[i] == f,
                            And(
                                s_times[i] >= friend["avail_start"],
                                e_times[i] <= friend["avail_end"],
                                e_times[i] - s_times[i] >= friend["min_duration"]
                            )))
    
    for i in range(n_slots - 1):
        opt.add(Implies(slots[i] == -1, slots[i+1] == -1))
    
    for i in range(n_slots):
        for j in range(i+1, n_slots):
            opt.add(Implies(And(slots[i] != -1, slots[j] != -1), slots[i] != slots[j]))
    
    for f in range(len(friends)):
        friend = friends[f]
        travel_time = travel[("Bayview", friend["location"])]
        opt.add(Implies(slots[0] == f, s_times[0] >= 540 + travel_time))
    
    for i in range(1, n_slots):
        for f_prev in range(len(friends)):
            for f_curr in range(len(friends)):
                travel_time = travel[(friends[f_prev]["location"], friends[f_curr]["location"])]
                opt.add(Implies(And(slots[i-1] == f_prev, slots[i] == f_curr),
                                s_times[i] >= e_times[i-1] + travel_time))
    
    meeting_count = Sum([If(slots[i] != -1, 1, 0) for i in range(n_slots)])
    opt.maximize(meeting_count)
    
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i in range(n_slots):
            slot_val = model.eval(slots[i]).as_long()
            if slot_val == -1:
                break
            friend = friends[slot_val]
            start_val = model.eval(s_times[i]).as_long()
            end_val = model.eval(e_times[i]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()