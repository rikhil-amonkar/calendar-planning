# Requires: pip install z3-solver
from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def solve():
    # Locations
    locations = ["Presidio", "Golden Gate Park", "Bayview", "Chinatown", "North Beach", "Mission District"]
    P = "Presidio"

    # Travel times (directed, in minutes)
    T = {
        "Presidio": {
            "Golden Gate Park": 12, "Bayview": 31, "Chinatown": 21, "North Beach": 18, "Mission District": 26
        },
        "Golden Gate Park": {
            "Presidio": 11, "Bayview": 23, "Chinatown": 23, "North Beach": 24, "Mission District": 17
        },
        "Bayview": {
            "Presidio": 31, "Golden Gate Park": 22, "Chinatown": 18, "North Beach": 21, "Mission District": 13
        },
        "Chinatown": {
            "Presidio": 19, "Golden Gate Park": 23, "Bayview": 22, "North Beach": 3, "Mission District": 18
        },
        "North Beach": {
            "Presidio": 17, "Golden Gate Park": 22, "Bayview": 22, "Chinatown": 6, "Mission District": 18
        },
        "Mission District": {
            "Presidio": 25, "Golden Gate Park": 17, "Bayview": 15, "Chinatown": 16, "North Beach": 17
        },
    }

    # Friends with location, availability window [start,end], and minimum meeting minutes
    friends = [
        # name, location, window_start, window_end, min_duration
        ("Jessica", "Golden Gate Park", to_minutes("13:45"), to_minutes("15:00"), 30),
        ("Ashley", "Bayview", to_minutes("17:15"), to_minutes("20:00"), 105),
        ("Ronald", "Chinatown", to_minutes("07:15"), to_minutes("14:45"), 90),
        ("William", "North Beach", to_minutes("13:15"), to_minutes("20:15"), 15),
        ("Daniel", "Mission District", to_minutes("07:00"), to_minutes("11:15"), 105),
    ]
    n = len(friends)

    # Start at Presidio at 09:00
    day_start = to_minutes("09:00")

    # Z3 model
    opt = Optimize()
    opt.set(priority='lex')  # Lexicographic optimization

    # Variables per friend
    start = {}
    end = {}
    dur = {}
    visited = {}
    pos = {}
    for i, (name, loc, ws, we, mind) in enumerate(friends):
        start[i] = Int(f"start_{i}")
        end[i] = Int(f"end_{i}")
        dur[i] = Int(f"dur_{i}")
        visited[i] = Bool(f"visited_{i}")
        pos[i] = Int(f"pos_{i}")
        # Domains
        opt.add(start[i] >= 0, start[i] <= 24*60)
        opt.add(end[i] >= 0, end[i] <= 24*60)
        opt.add(dur[i] >= 0, dur[i] <= 24*60)
        opt.add(pos[i] >= 0, pos[i] <= n)  # 0 means not visited; 1..n are order slots

        # Link visited with position
        opt.add(If(visited[i], pos[i] >= 1, pos[i] == 0))

        # If visited, enforce window and minimum duration and end = start + dur
        opt.add(If(visited[i],
                   And(start[i] >= ws,
                       end[i] <= we,
                       end[i] == start[i] + dur[i],
                       dur[i] >= mind),
                   And(start[i] == 0, end[i] == 0, dur[i] == 0)))

    # All-different positions among visited (allow 0 duplicates)
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Or(pos[i] == 0, pos[j] == 0, pos[i] != pos[j]))

    # No gaps in positions: if some friend is at k+1, someone must be at k
    for k in range(1, n):
        has_kp1 = Or(*[pos[i] == (k+1) for i in range(n)])
        has_k = Or(*[pos[i] == k for i in range(n)])
        opt.add(If(has_kp1, has_k, True))

    # Travel constraints for adjacency: if j follows i, start_j >= end_i + travel(i->j)
    for i, (name_i, loc_i, _, _, _) in enumerate(friends):
        for j, (name_j, loc_j, _, _, _) in enumerate(friends):
            if i == j:
                continue
            travel_ij = T[loc_i][loc_j]
            opt.add(If(And(visited[i], visited[j], pos[j] == pos[i] + 1),
                       start[j] >= end[i] + travel_ij,
                       True))

    # First meeting must be reachable from Presidio at 09:00
    for i, (name_i, loc_i, _, _, _) in enumerate(friends):
        travel_start = T[P][loc_i]
        opt.add(If(And(visited[i], pos[i] == 1),
                   start[i] >= day_start + travel_start,
                   True))

    # Define last_end as the maximum end among visited
    last_end = Int("last_end")
    opt.add(last_end >= 0, last_end <= 24*60)
    for i in range(n):
        opt.add(If(visited[i], last_end >= end[i], True))

    # Total visited count
    total_visited = Sum([If(visited[i], 1, 0) for i in range(n)])

    # Total slack between adjacent meetings
    slack_terms = []
    for i, (name_i, loc_i, _, _, _) in enumerate(friends):
        for j, (name_j, loc_j, _, _, _) in enumerate(friends):
            if i == j:
                continue
            travel_ij = T[loc_i][loc_j]
            # slack_ij is only active if j immediately follows i
            slack_ij = If(And(visited[i], visited[j], pos[j] == pos[i] + 1),
                          start[j] - (end[i] + travel_ij),
                          0)
            slack_terms.append(slack_ij)
    total_slack = Sum(slack_terms)

    # Total duration
    total_duration = Sum([dur[i] for i in range(n)])

    # Objectives:
    # 1) maximize number of friends met
    opt.maximize(total_visited)
    # 2) minimize day end time
    opt.minimize(last_end)
    # 3) minimize total waiting/slack between meetings
    opt.minimize(total_slack)
    # 4) maximize total time spent with friends
    opt.maximize(total_duration)
    # 5) tie-breakers to align with a compact plan
    #    prefer earlier end for Jessica and earlier start for William
    name_to_idx = {name: i for i, (name, *_rest) in enumerate(friends)}
    j_idx = name_to_idx["Jessica"]
    w_idx = name_to_idx["William"]
    opt.minimize(end[j_idx])
    opt.minimize(start[w_idx])

    # Solve
    if opt.check() != sat:
        raise RuntimeError("No feasible itinerary found.")

    m = opt.model()

    # Extract schedule sorted by position
    schedule = []
    entries = []
    for i, (name, loc, ws, we, mind) in enumerate(friends):
        if m.eval(visited[i]).is_true():
            s = m.eval(start[i]).as_long()
            e = m.eval(end[i]).as_long()
            p = m.eval(pos[i]).as_long()
            entries.append((p, name, s, e))
    entries.sort(key=lambda x: x[0])

    for p, name, s, e in entries:
        schedule.append({
            "action": "meet",
            "person": name,
            "start_time": to_hhmm(s),
            "end_time": to_hhmm(e)
        })

    return {"itinerary": schedule}

if __name__ == "__main__":
    result = solve()
    import json
    print(json.dumps(result, ensure_ascii=False))