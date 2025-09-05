#!/usr/bin/env python3
from z3 import *
import json
import sys

def minutes_to_time_str(m):
    total_minutes = m + 9 * 60
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    friends = [
        {"name": "Linda",   "location": "Marina District",      "avail_start": 540, "avail_end": 780, "duration": 30},
        {"name": "Kenneth", "location": "The Castro",           "avail_start": 345, "avail_end": 435, "duration": 30},
        {"name": "Kimberly","location": "Richmond District",    "avail_start": 315, "avail_end": 780, "duration": 30},
        {"name": "Paul",    "location": "Alamo Square",         "avail_start": 720, "avail_end": 750, "duration": 15},
        {"name": "Carol",   "location": "Financial District",   "avail_start": 75,  "avail_end": 180, "duration": 60},
        {"name": "Brian",   "location": "Presidio",             "avail_start": 60,  "avail_end": 750, "duration": 75},
        {"name": "Laura",   "location": "Mission District",     "avail_start": 435, "avail_end": 690, "duration": 30},
        {"name": "Sandra",  "location": "Nob Hill",             "avail_start": 15,  "avail_end": 570, "duration": 60},
        {"name": "Karen",   "location": "Russian Hill",         "avail_start": 570, "avail_end": 780, "duration": 75},
    ]
    num_friends = len(friends)
    
    travel_times = {
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Russian Hill"): 8,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Russian Hill"): 18,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Russian Hill"): 13,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Russian Hill"): 13,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Russian Hill"): 11,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Russian Hill"): 15,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Russian Hill"): 5,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Nob Hill"): 5,
    }
    
    locations = ["Pacific Heights", "Marina District", "The Castro", "Richmond District", 
                 "Alamo Square", "Financial District", "Presidio", "Mission District", 
                 "Nob Hill", "Russian Hill"]
    for loc in locations:
        travel_times[(loc, loc)] = 0

    max_slots = num_friends

    opt = Optimize()

    slots = [Int(f"slot_{k}") for k in range(max_slots)]
    starts = [Int(f"start_{k}") for k in range(max_slots)]
    
    for k in range(max_slots):
        opt.add(Or(slots[k] == -1, And(slots[k] >= 0, slots[k] < num_friends)))
        opt.add(starts[k] >= 0)
    
    for k in range(max_slots - 1):
        opt.add(Implies(slots[k] == -1, slots[k+1] == -1))
    
    for i in range(max_slots):
        for j in range(i+1, max_slots):
            opt.add(Implies(And(slots[i] != -1, slots[j] != -1), slots[i] != slots[j]))
    
    for k in range(max_slots):
        for i in range(num_friends):
            opt.add(Implies(slots[k] == i, starts[k] >= friends[i]["avail_start"]))
            opt.add(Implies(slots[k] == i, starts[k] + friends[i]["duration"] <= friends[i]["avail_end"]))
            if k == 0:
                opt.add(Implies(slots[0] == i,
                                starts[0] >= travel_times[("Pacific Heights", friends[i]["location"])]))
    
    for k in range(1, max_slots):
        for i in range(num_friends):
            for j in range(num_friends):
                travel_time = travel_times[(friends[j]["location"], friends[i]["location"])]
                opt.add(Implies(And(slots[k