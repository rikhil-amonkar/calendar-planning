#!/usr/bin/env python3
import json
from z3 import *

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    friends = [
        {"name": "Mark", "location": "Marina District", "avail_start": 18*60+45, "avail_end": 21*60, "min_duration": 90},
        {"name": "Karen", "location": "Financial District", "avail_start": 9*60+30, "avail_end": 12*60+45, "min_duration": 90},
        {"name": "Barbara", "location": "Alamo Square", "avail_start": 10*60, "avail_end": 19*60+30, "min_duration": 90},
        {"name": "Nancy", "location": "Golden Gate Park", "avail_start": 16*60+45, "avail_end": 20*60, "min_duration": 105},
        {"name": "David", "location": "The Castro", "avail_start": 9*60, "avail_end": 18*60, "min_duration": 120},
        {"name": "Linda", "location": "Bayview", "avail_start": 18*60+15, "avail_end": 19*60+45, "min_duration": 45},
        {"name": "Kevin", "location": "Sunset District", "avail_start": 10*60, "avail_end": 17*60+45, "min_duration": 120},
        {"name": "Matthew", "location": "Haight-Ashbury", "avail_start": 10*60+15, "avail_end": 15*60+30, "min_duration": 45},
        {"name": "Andrew", "location": "Nob Hill", "avail_start": 11*60+45, "avail_end": 16*60+45, "min_duration": 105}
    ]

    travel_times = {
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Nob Hill"): 5,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Sunset District"): 30,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Nob Hill"): 8,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Nob Hill"): 11,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Nob Hill"): 16,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Nob Hill"): 20,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Nob Hill"): 27,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Haight-Ashbury"): 13
    }

    n = len(friends)
    opt = Optimize()

    # Decision variables:
    # x_vars: if a friend is selected for a meeting
    # s_vars: meeting start time
    # e_vars: meeting end time
    x_vars = [Bool(f"x_{i}") for i in range(n)]
    s_vars = [Int(f"s_{i}") for i in range(n)]
    e_vars = [Int(f"e_{i}") for i in range(n)]

    # Add availability and duration constraints
    for i in range(n):
        friend = friends[i]
        avail_start = friend["avail_start"]
        avail_end = friend["avail_end"]
        min_dur = friend["min_duration"]
        opt.add(Implies(x_vars[i], s_vars[i] >= avail_start))
        opt.add(Implies(x_vars[i], e_vars[i] <= avail_end))
        opt.add(Implies(x_vars[i], e_vars[i] >= s_vars[i] + min_dur))
        opt.add(Implies(Not(x_vars[i]), s_vars[i] == 0))
        opt.add(Implies(Not(x_vars[i]), e_vars[i] == 0))
        opt.add(s_vars[i] >= 0)
        opt.add(e_vars[i] >= 0)

    # Add non-overlap constraints for pairs using travel times
    for i in range(n):
        for j in range(i+1, n):
            loc_i = friends[i]["location"]
            loc_j = friends[j]["location"]
            travel_i_j = travel_times[(loc_i