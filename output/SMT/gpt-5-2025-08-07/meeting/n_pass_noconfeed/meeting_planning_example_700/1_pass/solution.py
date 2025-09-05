import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    locations = [
        "Presidio",
        "Pacific Heights",
        "Golden Gate Park",
        "Fisherman's Wharf",
        "Marina District",
        "Alamo Square",
        "Sunset District",
        "Nob Hill",
        "North Beach",
    ]
    L = {name: i for i, name in enumerate(locations)}

    # Travel times (directed, in minutes)
    T = [[0 for _ in locations] for __ in locations]
    def set_t(a, b, v):
        T[L[a]][L[b]] = v

    # From the prompt (directed)
    set_t("Presidio", "Pacific Heights", 11)
    set_t("Presidio", "Golden Gate Park", 12)
    set_t("Presidio", "Fisherman's Wharf", 19)
    set_t("Presidio", "Marina District", 11)
    set_t("Presidio", "Alamo Square", 19)
    set_t("Presidio", "Sunset District", 15)
    set_t("Presidio", "Nob Hill", 18)
    set_t("Presidio", "North Beach", 18)

    set_t("Pacific Heights", "Presidio", 11)
    set_t("Pacific Heights", "Golden Gate Park", 15)
    set_t("Pacific Heights", "Fisherman's Wharf", 13)
    set_t("Pacific Heights", "Marina District", 6)
    set_t("Pacific Heights", "Alamo Square", 10)
    set_t("Pacific Heights", "Sunset District", 21)
    set_t("Pacific Heights", "Nob Hill", 8)
    set_t("Pacific Heights", "North Beach", 9)

    set_t("Golden Gate Park", "Presidio", 11)
    set_t("Golden Gate Park", "Pacific Heights", 16)
    set_t("Golden Gate Park", "Fisherman's Wharf", 24)
    set_t("Golden Gate Park", "Marina District", 16)
    set_t("Golden Gate Park", "Alamo Square", 9)
    set_t("Golden Gate Park", "Sunset District", 10)
    set_t("Golden Gate Park", "Nob Hill", 20)
    set_t("Golden Gate Park", "North Beach", 23)

    set_t("Fisherman's Wharf", "Presidio", 17)
    set_t("Fisherman's Wharf", "Pacific Heights", 12)
    set_t("Fisherman's Wharf", "Golden Gate Park", 25)
    set_t("Fisherman's Wharf", "Marina District", 9)
    set_t("Fisherman's Wharf", "Alamo Square", 21)
    set_t("Fisherman's Wharf", "Sunset District", 27)
    set_t("Fisherman's Wharf", "Nob Hill", 11)
    set_t("Fisherman's Wharf", "North Beach", 6)

    set_t("Marina District", "Presidio", 10)
    set_t("Marina District", "Pacific Heights", 7)
    set_t("Marina District", "Golden Gate Park", 18)
    set_t("Marina District", "Fisherman's Wharf", 10)
    set_t("Marina District", "Alamo Square", 15)
    set_t("Marina District", "Sunset District", 19)
    set_t("Marina District", "Nob Hill", 12)
    set_t("Marina District", "North Beach", 11)

    set_t("Alamo Square", "Presidio", 17)
    set_t("Alamo Square", "Pacific Heights", 10)
    set_t("Alamo Square", "Golden Gate Park", 9)
    set_t("Alamo Square", "Fisherman's Wharf", 19)
    set_t("Alamo Square", "Marina District", 15)
    set_t("Alamo Square", "Sunset District", 16)
    set_t("Alamo Square", "Nob Hill", 11)
    set_t("Alamo Square", "North Beach", 15)

    set_t("Sunset District", "Presidio", 16)
    set_t("Sunset District", "Pacific Heights", 21)
    set_t("Sunset District", "Golden Gate Park", 11)
    set_t("Sunset District", "Fisherman's Wharf", 29)
    set_t("Sunset District", "Marina District", 21)
    set_t("Sunset District", "Alamo Square", 17)
    set_t("Sunset District", "Nob Hill", 27)
    set_t("Sunset District", "North Beach", 28)

    set_t("Nob Hill", "Presidio", 17)
    set_t("Nob Hill", "Pacific Heights", 8)
    set_t("Nob Hill", "Golden Gate Park", 17)
    set_t("Nob Hill", "Fisherman's Wharf", 10)
    set_t("Nob Hill", "Marina District", 11)
    set_t("Nob Hill", "Alamo Square", 11)
    set_t("Nob Hill", "Sunset District", 24)
    set_t("Nob Hill", "North Beach", 8)

    set_t("North Beach", "Presidio", 17)
    set_t("North Beach", "Pacific Heights", 8)
    set_t("North Beach", "Golden Gate Park", 22)
    set_t("North Beach", "Fisherman's Wharf", 5)
    set_t("North Beach", "Marina District", 9)
    set_t("North Beach", "Alamo Square", 16)
    set_t("North Beach", "Sunset District", 27)
    set_t("North Beach", "Nob Hill", 7)

    # Friends and their constraints
    friends = [
        {"name": "Kevin",    "location": "Pacific Heights",   "start": minutes(7,15),  "end": minutes(8,45),  "min_dur": 90},
        {"name": "Michelle", "location": "Golden Gate Park",   "start": minutes(20,0),  "end": minutes(21,0),  "min_dur": 15},
        {"name": "Emily",    "location": "Fisherman's Wharf",  "start": minutes(16,15), "end": minutes(19,0),  "min_dur": 30},
        {"name": "Mark",     "location": "Marina District",    "start": minutes(18,15), "end": minutes(19,45), "min_dur": 75},
        {"name": "Barbara",  "location": "Alamo Square",       "start": minutes(17,0),  "end": minutes(19,0),  "min_dur": 120},
        {"name": "Laura",    "location": "Sunset District",    "start": minutes(19,0),  "end": minutes(21,15), "min_dur": 75},
        {"name": "Mary",     "location": "Nob Hill",           "start": minutes(17,30), "end": minutes(19,0),  "min_dur": 45},
        {"name": "Helen",    "location": "North Beach",        "start": minutes(11,0),  "end": minutes(12,15), "min_dur": 45},
    ]
    n_friends = len(friends)
    loc_idx = [L[f["location"]] for f in friends]
    avail_start = [f["start"] for f in friends]
    avail_end = [f["end"] for f in friends]
    min_dur = [f["min_dur"] for f in friends]

    # Planning horizon
    day_start_loc = "Presidio"
    arrival_time = minutes(9, 0)
    max_time = 24 * 60

    # Number of slots (at most one per friend)
    SLOTS = n_friends

    # Z3 variables
    friend_idx = [Int(f"friend_{i}") for i in range(SLOTS)]      # -1 means unused, otherwise 0..n_friends-1
    start_time = [Int(f"start_{i}") for i in range(SLOTS)]
    end_time = [Int(f"end_{i}") for i in range(SLOTS)]

    opt = Optimize()
    opt.set(priority='lex')

    # Domains and basic constraints
    for i in range(SLOTS):
        opt.add(friend_idx[i] >= -1, friend_idx[i] < n_friends)
        opt.add(start_time[i] >= 0, start_time[i] <= max_time)
        opt.add(end_time[i] >= 0, end_time[i] <= max_time)

    # Prefix property: once a slot is unused, all following are unused
    for i in range(1, SLOTS):
        opt.add(Implies(friend_idx[i] != -1, friend_idx[i-1] != -1))

    # No friend appears more than once
    for i in range(SLOTS):
        for j in range(i+1, SLOTS):
            opt.add(Not(And(friend_idx[i] != -1, friend_idx[j] != -1, friend_idx[i] == friend_idx[j])))

    # Helper: piecewise lookups
    def pw_value(idx_expr, values):
        # returns an IntExpr equal to values[idx_expr] if idx_expr != -1, else 0 (we'll guard by usage anyway)
        terms = [If(idx_expr == k, values[k], 0) for k in range(n_friends)]
        return Sum(terms)

    def travel_from_presidio(idx_expr):
        # Travel time from Presidio to friend's location
        times = [T[L[day_start_loc]][loc_idx[k]] for k in range(n_friends)]
        return pw_value(idx_expr, times)

    def travel_between(idx_expr_prev, idx_expr_cur):
        # Travel time between two consecutive meetings based on chosen friends
        terms = []
        for a in range(n_friends):
            for b in range(n_friends):
                terms.append(If(And(idx_expr_prev == a, idx_expr_cur == b), T[loc_idx[a]][loc_idx[b]], 0))
        return Sum(terms)

    # Meeting window and duration constraints
    for i in range(SLOTS):
        # For each possible friend assignment, enforce window and duration
        for f_idx in range(n_friends):
            opt.add(Implies(friend_idx[i] == f_idx,
                            And(start_time[i] >= avail_start[f_idx],
                                end_time[i] <= avail_end[f_idx],
                                end_time[i] - start_time[i] >= min_dur[f_idx],
                                start_time[i] < end_time[i])))

    # Initial travel from Presidio and ordering/travel constraints
    if SLOTS > 0:
        opt.add(Implies(friend_idx[0] != -1,
                        start_time[0] >= arrival_time + travel_from_presidio(friend_idx[0])))

    for i in range(1, SLOTS):
        # If slot i is used, ensure sufficient travel time from previous slot
        opt.add(Implies(friend_idx[i] != -1,
                        start_time[i] >= end_time[i-1] + travel_between(friend_idx[i-1], friend_idx[i])))

    # Objectives: maximize number of meetings, then total meeting time
    count_used = Sum([If(friend_idx[i] != -1, 1, 0) for i in range(SLOTS)])
    total_meeting_time = Sum([If(friend_idx[i] != -1, end_time[i] - start_time[i], 0) for i in range(SLOTS)])
    opt.maximize(count_used)
    opt.maximize(total_meeting_time)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = opt.model()

    itinerary = []
    for i in range(SLOTS):
        fi = m.eval(friend_idx[i]).as_long()
        if fi == -1:
            break
        st = m.eval(start_time[i]).as_long()
        et = m.eval(end_time[i]).as_long()
        itinerary.append({
            "action": "meet",
            "location": friends[fi]["location"],
            "person": friends[fi]["name"],
            "start_time": fmt_time(st),
            "end_time": fmt_time(et)
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()