import json
from functools import lru_cache

# Helper functions for time conversion
def to_minutes(tstr):
    # tstr like '9:00' or '13:30'
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Build directed travel-time matrix (in minutes)
L = [
    "Financial District",
    "Russian Hill",
    "Sunset District",
    "North Beach",
    "The Castro",
    "Golden Gate Park",
]

travel = {a: {} for a in L}
def set_t(a,b,t): travel[a][b]=t

set_t("Financial District","Russian Hill",10)
set_t("Financial District","Sunset District",31)
set_t("Financial District","North Beach",7)
set_t("Financial District","The Castro",23)
set_t("Financial District","Golden Gate Park",23)

set_t("Russian Hill","Financial District",11)
set_t("Russian Hill","Sunset District",23)
set_t("Russian Hill","North Beach",5)
set_t("Russian Hill","The Castro",21)
set_t("Russian Hill","Golden Gate Park",21)

set_t("Sunset District","Financial District",30)
set_t("Sunset District","Russian Hill",24)
set_t("Sunset District","North Beach",29)
set_t("Sunset District","The Castro",17)
set_t("Sunset District","Golden Gate Park",11)

set_t("North Beach","Financial District",8)
set_t("North Beach","Russian Hill",4)
set_t("North Beach","Sunset District",27)
set_t("North Beach","The Castro",22)
set_t("North Beach","Golden Gate Park",22)

set_t("The Castro","Financial District",20)
set_t("The Castro","Russian Hill",18)
set_t("The Castro","Sunset District",17)
set_t("The Castro","North Beach",20)
set_t("The Castro","Golden Gate Park",11)

set_t("Golden Gate Park","Financial District",26)
set_t("Golden Gate Park","Russian Hill",19)
set_t("Golden Gate Park","Sunset District",10)
set_t("Golden Gate Park","North Beach",24)
set_t("Golden Gate Park","The Castro",13)

# Friends data: location, availability window [start,end), min required minutes
friends = {
    "Ronald": {
        "location": "Russian Hill",
        "start": to_minutes("13:45"),
        "end": to_minutes("17:15"),
        "need": 105
    },
    "Patricia": {
        "location": "Sunset District",
        "start": to_minutes("9:15"),
        "end": to_minutes("22:00"),
        "need": 60
    },
    "Laura": {
        "location": "North Beach",
        "start": to_minutes("12:30"),
        "end": to_minutes("12:45"),
        "need": 15
    },
    "Emily": {
        "location": "The Castro",
        "start": to_minutes("16:15"),
        "end": to_minutes("18:30"),
        "need": 60
    },
    "Mary": {
        "location": "Golden Gate Park",
        "start": to_minutes("15:00"),
        "end": to_minutes("16:30"),
        "need": 60
    }
}

friend_names = list(friends.keys())

# Start state
start_location = "Financial District"
start_time = to_minutes("9:00")

# Quick feasibility check for each friend individually from a given state
def individual_possible(current_loc, current_time, name, remaining):
    f = friends[name]
    t_travel = travel[current_loc][f["location"]]
    arrive = current_time + t_travel
    start = max(arrive, f["start"])
    # Maximum we can still spend with this friend starting ASAP (not counting leaving and coming back)
    if start >= f["end"]:
        return 0
    return max(0, f["end"] - start)

# Upper bound on additional friends attainable from a state (ignoring conflicts)
def upper_bound_met_count(current_loc, current_time, remaining):
    ub = 0
    for i, name in enumerate(friend_names):
        r = remaining[i]
        if r <= 0:
            ub += 1
        else:
            # If we can't get even r minutes from now with direct visit, it's impossible to meet them fully
            max_single_visit = individual_possible(current_loc, current_time, name, r)
            if max_single_visit >= 1:  # still could get some minutes; but we need at least r total possibly via multiple visits
                # Also check absolute possible window remainder anywhere (best case we teleport immediately to them)
                f = friends[name]
                # Teleport-based maximum possible from now is simply max(0, f.end - max(current_time, f.start))
                teleport_max = max(0, f["end"] - max(current_time, f["start"]))
                if teleport_max >= r:
                    pass
                else:
                    # At least prune if even teleporting can't satisfy remaining
                    continue
            else:
                continue
    # ub is not counting those not yet fully met; compute optimistic count as those with r<=0 plus those for which teleport could allow completion
    optimistic = 0
    for i, name in enumerate(friend_names):
        r = remaining[i]
        if r <= 0:
            optimistic += 1
        else:
            f = friends[name]
            if max(0, f["end"] - max(current_time, f["start"])) >= r:
                optimistic += 1
    return optimistic

best_solution = {
    "met_count": -1,
    "finish_time": None,
    "travel_time": None,
    "itinerary": None
}

# DFS with branch-and-bound; allow splitting meetings
def dfs(current_loc, current_time, remaining, itinerary, total_travel):
    global best_solution

    # Prune if even optimistic bound cannot beat current best
    optimistic = upper_bound_met_count(current_loc, current_time, remaining)
    if optimistic < best_solution["met_count"]:
        return

    # Generate candidate next actions
    actions = []
    for i, name in enumerate(friend_names):
        rem = remaining[i]
        if rem <= 0:
            continue
        f = friends[name]
        # compute arrival time
        t_travel = travel[current_loc][f["location"]]
        arrive = current_time + t_travel
        if arrive >= f["end"]:
            continue  # can't meet at all
        start = max(arrive, f["start"])
        max_meet_now = min(rem, f["end"] - start)
        if max_meet_now <= 0:
            continue

        # Determine candidate durations
        durations = set()
        # Option 1: meet as much as possible now (either finish this friend or until their window closes)
        durations.add(max_meet_now)

        # Option 2: end early enough to fully meet another friend's remaining need later
        for j, other in enumerate(friend_names):
            if j == i:
                continue
            r_other = remaining[j]
            if r_other <= 0:
                continue
            g = friends[other]
            # latest time we must ARRIVE at g to still meet r_other
            latest_arrival_for_full = g["end"] - r_other
            # To arrive by that, we must depart current friend by:
            latest_depart_from_f = latest_arrival_for_full - travel[f["location"]][g["location"]]
            # We can wait at g if we arrive earlier than g.start; this constraint is sufficient
            # So meeting duration <= latest_depart_from_f - start
            dur = min(max_meet_now, max(0, latest_depart_from_f - start))
            if dur > 0:
                durations.add(dur)

        # Add sorted durations (shorter first to explore more flexible splits early)
        for d in sorted(durations):
            actions.append((i, name, f["location"], start, d, t_travel))

    # If no more actions feasible, evaluate current plan
    if not actions:
        met = sum(1 for r in remaining if r <= 0)
        finish_time = current_time
        # Update best if improved
        improved = False
        if met > best_solution["met_count"]:
            improved = True
        elif met == best_solution["met_count"]:
            if best_solution["finish_time"] is None or finish_time < best_solution["finish_time"]:
                improved = True
            elif finish_time == best_solution["finish_time"] and total_travel < (best_solution["travel_time"] or 10**9):
                improved = True

        if improved:
            best_solution["met_count"] = met
            best_solution["finish_time"] = finish_time
            best_solution["travel_time"] = total_travel
            best_solution["itinerary"] = list(itinerary)
        return

    # Explore actions
    for (idx, name, loc, start, d, t_travel) in actions:
        f = friends[name]
        new_remaining = list(remaining)
        new_remaining[idx] = max(0, new_remaining[idx] - d)
        # Append meet action
        new_itinerary = list(itinerary)
        new_itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": start,
            "end_time": start + d
        })
        # Recurse
        dfs(loc, start + d, tuple(new_remaining), new_itinerary, total_travel + t_travel)

# Initialize remaining required minutes
initial_remaining = tuple(friends[name]["need"] for name in friend_names)

# Kick off search
dfs(start_location, start_time, initial_remaining, [], 0)

# Prepare JSON output
output = {"itinerary": []}
if best_solution["itinerary"] is not None:
    for item in best_solution["itinerary"]:
        output["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": to_hhmm(item["start_time"]),
            "end_time": to_hhmm(item["end_time"])
        })

print(json.dumps(output, ensure_ascii=False, indent=2))