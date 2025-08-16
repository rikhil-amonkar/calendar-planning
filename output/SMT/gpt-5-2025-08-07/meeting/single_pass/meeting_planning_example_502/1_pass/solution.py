# pip install z3-solver
from z3 import Optimize, Int, sat
import itertools, json

def minutes(h, m=0):
    return 60*h + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Travel times (minutes), as given
travel = {
    "Financial District": {
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Union Square": 9,
        "Fisherman's Wharf": 10,
        "Pacific Heights": 13,
        "North Beach": 7
    },
    "Golden Gate Park": {
        "Financial District": 26,
        "Chinatown": 23,
        "Union Square": 22,
        "Fisherman's Wharf": 24,
        "Pacific Heights": 16,
        "North Beach": 24
    },
    "Chinatown": {
        "Financial District": 5,
        "Golden Gate Park": 23,
        "Union Square": 7,
        "Fisherman's Wharf": 8,
        "Pacific Heights": 10,
        "North Beach": 3
    },
    "Union Square": {
        "Financial District": 9,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Fisherman's Wharf": 15,
        "Pacific Heights": 15,
        "North Beach": 10
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Union Square": 13,
        "Pacific Heights": 12,
        "North Beach": 6
    },
    "Pacific Heights": {
        "Financial District": 13,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Union Square": 12,
        "Fisherman's Wharf": 13,
        "North Beach": 9
    },
    "North Beach": {
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Chinatown": 6,
        "Union Square": 7,
        "Fisherman's Wharf": 5,
        "Pacific Heights": 8
    }
}

# Friends with windows and minimum durations
friends = [
    {"name":"Stephanie", "loc":"Golden Gate Park",    "start":minutes(11,0), "end":minutes(15,0),  "min_dur":105},
    {"name":"Karen",     "loc":"Chinatown",           "start":minutes(13,45),"end":minutes(16,30), "min_dur":15},
    {"name":"Brian",     "loc":"Union Square",        "start":minutes(15,0), "end":minutes(17,15), "min_dur":30},
    {"name":"Rebecca",   "loc":"Fisherman's Wharf",   "start":minutes(8,0),  "end":minutes(11,15), "min_dur":30},
    {"name":"Joseph",    "loc":"Pacific Heights",     "start":minutes(8,15), "end":minutes(9,30),  "min_dur":60},
    {"name":"Steven",    "loc":"North Beach",         "start":minutes(14,30),"end":minutes(20,45), "min_dur":120},
]

FD_ARRIVAL = minutes(9,0)

def solve_for_order(order):
    opt = Optimize()
    start_vars = []
    end_vars = []

    for i, f in enumerate(order):
        s = Int(f"s_{i}")
        e = Int(f"e_{i}")
        # time window and duration
        opt.add(s >= f["start"])
        opt.add(e == s + f["min_dur"])
        opt.add(e <= f["end"])
        # domain
        opt.add(s >= 0, s <= 24*60, e >= 0, e <= 24*60)
        start_vars.append(s)
        end_vars.append(e)

    if order:
        # From FD to first friend
        opt.add(start_vars[0] >= FD_ARRIVAL + travel["Financial District"][order[0]["loc"]])
        # Sequencing with travel
        for i in range(len(order)-1):
            opt.add(start_vars[i+1] >= end_vars[i] + travel[order[i]["loc"]][order[i+1]["loc"]])
        # Objective: minimize finish time of last meeting
        opt.minimize(end_vars[-1])

    if opt.check() != sat:
        return None

    m = opt.model()
    itinerary = []
    for i, f in enumerate(order):
        st = m[start_vars[i]].as_long()
        en = m[end_vars[i]].as_long()
        itinerary.append({"name": f["name"], "start": st, "end": en})
    last_end = itinerary[-1]["end"] if itinerary else FD_ARRIVAL
    return {"itinerary": itinerary, "last_end": last_end}

def find_best_schedule():
    best = None
    best_count = -1
    best_end = 10**9

    # try largest subsets first
    n = len(friends)
    for k in range(n, 0, -1):
        any_found = False
        for subset in itertools.combinations(friends, k):
            # Explore all orders
            for perm in itertools.permutations(subset):
                res = solve_for_order(list(perm))
                if res is None:
                    continue
                any_found = True
                if k > best_count or (k == best_count and res["last_end"] < best_end):
                    best = res
                    best_count = k
                    best_end = res["last_end"]
        if any_found:
            break
    return best

def main():
    res = find_best_schedule()
    out = {"itinerary": []}
    if res:
        for m in res["itinerary"]:
            out["itinerary"].append({
                "action": "meet",
                "person": m["name"],
                "start_time": fmt_time(m["start"]),
                "end_time": fmt_time(m["end"])
            })
    print(json.dumps(out))

if __name__ == "__main__":
    main()