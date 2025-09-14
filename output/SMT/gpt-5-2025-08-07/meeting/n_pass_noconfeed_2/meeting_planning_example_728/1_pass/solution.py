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
        "Marina District",
        "Mission District",
        "Fisherman's Wharf",
        "Presidio",
        "Union Square",
        "Sunset District",
        "Financial District",
        "Haight-Ashbury",
        "Russian Hill",
    ]
    loc_index = {name: i for i, name in enumerate(locations)}

    # Travel times (in minutes), as given (asymmetric)
    T = {name: {} for name in locations}
    def set_t(a, b, t):
        T[a][b] = t

    # Populate travel times
    set_t("Marina District", "Mission District", 20)
    set_t("Marina District", "Fisherman's Wharf", 10)
    set_t("Marina District", "Presidio", 10)
    set_t("Marina District", "Union Square", 16)
    set_t("Marina District", "Sunset District", 19)
    set_t("Marina District", "Financial District", 17)
    set_t("Marina District", "Haight-Ashbury", 16)
    set_t("Marina District", "Russian Hill", 8)

    set_t("Mission District", "Marina District", 19)
    set_t("Mission District", "Fisherman's Wharf", 22)
    set_t("Mission District", "Presidio", 25)
    set_t("Mission District", "Union Square", 15)
    set_t("Mission District", "Sunset District", 24)
    set_t("Mission District", "Financial District", 15)
    set_t("Mission District", "Haight-Ashbury", 12)
    set_t("Mission District", "Russian Hill", 15)

    set_t("Fisherman's Wharf", "Marina District", 9)
    set_t("Fisherman's Wharf", "Mission District", 22)
    set_t("Fisherman's Wharf", "Presidio", 17)
    set_t("Fisherman's Wharf", "Union Square", 13)
    set_t("Fisherman's Wharf", "Sunset District", 27)
    set_t("Fisherman's Wharf", "Financial District", 11)
    set_t("Fisherman's Wharf", "Haight-Ashbury", 22)
    set_t("Fisherman's Wharf", "Russian Hill", 7)

    set_t("Presidio", "Marina District", 11)
    set_t("Presidio", "Mission District", 26)
    set_t("Presidio", "Fisherman's Wharf", 19)
    set_t("Presidio", "Union Square", 22)
    set_t("Presidio", "Sunset District", 15)
    set_t("Presidio", "Financial District", 23)
    set_t("Presidio", "Haight-Ashbury", 15)
    set_t("Presidio", "Russian Hill", 14)

    set_t("Union Square", "Marina District", 18)
    set_t("Union Square", "Mission District", 14)
    set_t("Union Square", "Fisherman's Wharf", 15)
    set_t("Union Square", "Presidio", 24)
    set_t("Union Square", "Sunset District", 27)
    set_t("Union Square", "Financial District", 9)
    set_t("Union Square", "Haight-Ashbury", 18)
    set_t("Union Square", "Russian Hill", 13)

    set_t("Sunset District", "Marina District", 21)
    set_t("Sunset District", "Mission District", 25)
    set_t("Sunset District", "Fisherman's Wharf", 29)
    set_t("Sunset District", "Presidio", 16)
    set_t("Sunset District", "Union Square", 30)
    set_t("Sunset District", "Financial District", 30)
    set_t("Sunset District", "Haight-Ashbury", 15)
    set_t("Sunset District", "Russian Hill", 24)

    set_t("Financial District", "Marina District", 15)
    set_t("Financial District", "Mission District", 17)
    set_t("Financial District", "Fisherman's Wharf", 10)
    set_t("Financial District", "Presidio", 22)
    set_t("Financial District", "Union Square", 9)
    set_t("Financial District", "Sunset District", 30)
    set_t("Financial District", "Haight-Ashbury", 19)
    set_t("Financial District", "Russian Hill", 11)

    set_t("Haight-Ashbury", "Marina District", 17)
    set_t("Haight-Ashbury", "Mission District", 11)
    set_t("Haight-Ashbury", "Fisherman's Wharf", 23)
    set_t("Haight-Ashbury", "Presidio", 15)
    set_t("Haight-Ashbury", "Union Square", 19)
    set_t("Haight-Ashbury", "Sunset District", 15)
    set_t("Haight-Ashbury", "Financial District", 21)
    set_t("Haight-Ashbury", "Russian Hill", 17)

    set_t("Russian Hill", "Marina District", 7)
    set_t("Russian Hill", "Mission District", 16)
    set_t("Russian Hill", "Fisherman's Wharf", 7)
    set_t("Russian Hill", "Presidio", 14)
    set_t("Russian Hill", "Union Square", 10)
    set_t("Russian Hill", "Sunset District", 23)
    set_t("Russian Hill", "Financial District", 11)
    set_t("Russian Hill", "Haight-Ashbury", 17)

    # Friends with availability and minimum meeting durations
    friends = [
        {"name": "Karen", "location": "Mission District", "start": minutes(14,15), "end": minutes(22,0), "min": 30},
        {"name": "Richard", "location": "Fisherman's Wharf", "start": minutes(14,30), "end": minutes(17,30), "min": 30},
        {"name": "Robert", "location": "Presidio", "start": minutes(21,45), "end": minutes(22,45), "min": 60},
        {"name": "Joseph", "location": "Union Square", "start": minutes(11,45), "end": minutes(14,45), "min": 120},
        {"name": "Helen", "location": "Sunset District", "start": minutes(14,45), "end": minutes(20,45), "min": 105},
        {"name": "Elizabeth", "location": "Financial District", "start": minutes(10,0), "end": minutes(12,45), "min": 75},
        {"name": "Kimberly", "location": "Haight-Ashbury", "start": minutes(14,15), "end": minutes(17,30), "min": 105},
        {"name": "Ashley", "location": "Russian Hill", "start": minutes(11,30), "end": minutes(21,30), "min": 45},
    ]
    num_friends = len(friends)

    # Precompute arrays indexed by friend id
    friend_loc = [friends[i]["location"] for i in range(num_friends)]
    friend_start = [friends[i]["start"] for i in range(num_friends)]
    friend_end = [friends[i]["end"] for i in range(num_friends)]
    friend_min = [friends[i]["min"] for i in range(num_friends)]

    # Day start location/time
    start_location = "Marina District"
    arrival_time_at_start = minutes(9, 0)

    # SMT variables
    N = num_friends  # maximum number of meeting slots
    used = [Bool(f"used_{i}") for i in range(N)]
    who = [Int(f"who_{i}") for i in range(N)]  # -1 if unused, else friend id 0..num_friends-1
    start_t = [Int(f"start_{i}") for i in range(N)]
    end_t = [Int(f"end_{i}") for i in range(N)]

    o = Optimize()

    for i in range(N):
        # Domain constraints
        o.add(Or(And(used[i], who[i] >= 0, who[i] < num_friends), And(Not(used[i]), who[i] == -1)))
        o.add(start_t[i] >= 0)
        o.add(end_t[i] >= 0)
        o.add(end_t[i] >= start_t[i])

    # Prefix (no gaps): if slot i not used, then all later slots are not used
    for i in range(1, N):
        o.add(Implies(Not(used[i-1]), Not(used[i])))

    # Distinct friends across used slots
    for i in range(N):
        for j in range(i+1, N):
            o.add(Implies(And(used[i], used[j]), who[i] != who[j]))

    # Meeting window and duration constraints conditional on selected friend
    for i in range(N):
        conds = []
        for k in range(num_friends):
            conds.append(And(
                who[i] == k,
                start_t[i] >= friend_start[k],
                end_t[i] <= friend_end[k],
                end_t[i] - start_t[i] >= friend_min[k],
            ))
        o.add(Implies(used[i], Or(*conds)))

    # Travel constraints
    # First used slot: from Marina District at 9:00
    first_travel_conds = []
    for k in range(num_friends):
        tt = T[start_location][friend_loc[k]]
        first_travel_conds.append(And(who[0] == k, start_t[0] >= arrival_time_at_start + tt))
    o.add(Implies(used[0], Or(*first_travel_conds)))

    # Subsequent slots: travel from previous meeting location
    for i in range(1, N):
        pair_conds = []
        for kp in range(num_friends):
            for kc in range(num_friends):
                tt = T[friend_loc[kp]][friend_loc[kc]]
                pair_conds.append(And(who[i-1] == kp, who[i] == kc, start_t[i] >= end_t[i-1] + tt))
        o.add(Implies(And(used[i], used[i-1]), Or(*pair_conds)))

    # Objective: maximize number of meetings
    total_meetings = Sum([If(used[i], 1, 0) for i in range(N)])
    o.maximize(total_meetings)

    # Secondary objective: minimize sum of end times (encourage earlier finish / less slack)
    o.minimize(Sum([If(used[i], end_t[i], 0) for i in range(N)]))

    if o.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = o.model()

    itinerary = []
    for i in range(N):
        if m.evaluate(used[i]).is_true():
            fid = m.evaluate(who[i]).as_long()
            st = m.evaluate(start_t[i]).as_long()
            et = m.evaluate(end_t[i]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friend_loc[fid],
                "person": friends[fid]["name"],
                "start_time": fmt_time(st),
                "end_time": fmt_time(et),
            })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()