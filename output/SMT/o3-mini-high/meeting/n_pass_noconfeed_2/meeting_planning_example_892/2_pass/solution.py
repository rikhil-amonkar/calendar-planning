from z3 import *
import json

def minutes_to_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    travel = {
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Embarcadero"): 14,
        
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Sunset District"): 23,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Nob Hill"): 20,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "North Beach"): 22,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Embarcadero"): 19,
        
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Nob Hill"): 27,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Embarcadero"): 30,
        
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Bayview"): 27,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Embarcadero"): 19,
        
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Bayview"): 19,
        ("Nob Hill", "Sunset District"): 24,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Embarcadero"): 9,
        
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Bayview"): 20,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Embarcadero"): 5,
        
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Embarcadero"): 20,
        
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Bayview"): 25,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Embarcadero"): 6,
        
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Embarcadero"): 8,
        
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Russian Hill"): 8,
    }
    
    locations = {"Marina District", "Bayview", "Sunset District", "Richmond District", 
                 "Nob Hill", "Chinatown", "Haight-Ashbury", "North Beach", 
                 "Russian Hill", "Embarcadero"}
    for loc in locations:
        travel[(loc, loc)] = 0

    friends = [
        {"name": "Charles", "location": "Bayview", "avail_start": 690, "avail_end": 870, "min_duration": 45},
        {"name": "Robert", "location": "Sunset District", "avail_start": 1005, "avail_end": 1260, "min_duration": 30},
        {"name": "Karen", "location": "Richmond District", "avail_start": 1155, "avail_end": 1290, "min_duration": 60},
        {"name": "Rebecca", "location": "Nob Hill", "avail_start": 975, "avail_end": 1230, "min_duration": 90},
        {"name": "Margaret", "location": "Chinatown", "avail_start": 855, "avail_end": 1185, "min_duration": 120},
        {"name": "Patricia", "location": "Haight-Ashbury", "avail_start": 870, "avail_end": 1230, "min_duration": 45},
        {"name": "Mark", "location": "North Beach", "avail_start": 840, "avail_end": 1110, "min_duration": 105},
        {"name": "Melissa", "location": "Russian Hill", "avail_start": 780, "avail_end": 1185, "min_duration": 30},
        {"name": "Laura", "location": "Embarcadero", "avail_start": 465, "avail_end": 795, "min_duration": 105},
    ]
    
    num_friends = len(friends)
    
    s_vars = []
    e_vars = []
    order_vars = []
    sched_vars = []
    
    opt = Optimize()
    
    arrival_time = 540
    
    for i, friend in enumerate(friends):
        s_i = Int(f"s_{friend['name']}")
        e_i = Int(f"e_{friend['name']}")
        order_i = Int(f"order_{friend['name']}")
        sched_i = Bool(f"sched_{friend['name']}")
        s_vars.append(s_i)
        e_vars.append(e_i)
        order_vars.append(order_i)
        sched_vars.append(sched_i)
        
        initial_arrival = arrival_time + travel[("Marina District", friend["location"])]
        
        opt.add(Implies(sched_i, s_i >= friend["avail_start"]))
        opt.add(Implies(sched_i, s_i >= initial_arrival))
        opt.add(Implies(sched_i, e_i == s_i + friend["min_duration"]))
        opt.add(Implies(sched_i, e_i <= friend["avail_end"]))
        
        opt.add(Implies(Not(sched_i), s_i == 0))
        opt.add(Implies(Not(sched_i), e_i == 0))
        opt.add(Implies(Not(sched_i), order_i == -