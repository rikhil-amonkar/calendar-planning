import json
from z3 import Int, Bool, If, And, Or, Implies, Optimize, sat

def time_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Locations
    SUNSET = "Sunset District"
    CHINATOWN = "Chinatown"
    RUSSIAN_HILL = "Russian Hill"
    NORTH_BEACH = "North Beach"

    # Travel times in minutes (directed)
    travel = {
        SUNSET:       {CHINATOWN: 30, RUSSIAN_HILL: 24, NORTH_BEACH: 29},
        CHINATOWN:    {SUNSET: 29, RUSSIAN_HILL: 7,  NORTH_BEACH: 3},
        RUSSIAN_HILL: {SUNSET: 23, CHINATOWN: 9,     NORTH_BEACH: 5},
        NORTH_BEACH:  {SUNSET: 27, CHINATOWN: 6,     RUSSIAN_HILL: 4},
    }

    def t(frm, to):
        return travel[frm][to]

    # Day start arrival
    arrive_time = 9*60  # 9:00

    # People and constraints
    people = [
        {
            "name": "Melissa",
            "location": NORTH_BEACH,
            "window_start": 8*60 + 15,   # 8:15
            "window_end":   13*60 + 30,  # 13:30
            "min_duration": 105
        },
        {
            "name": "Anthony",
            "location": CHINATOWN,
            "window_start": 13*60 + 15,  # 13:15
            "window_end":   14*60 + 30,  # 14:30
            "min_duration": 60
        },
        {
            "name": "Rebecca",
            "location": RUSSIAN_HILL,
            "window_start": 19*60 + 30,  # 19:30
            "window_end":   21*60 + 15,  # 21:15
            "min_duration": 105
        },
    ]

    n = len(people)

    # Z3 variables
    s = [Int(f"s_{i}") for i in range(n)]
    e = [Int(f"e_{i}") for i in range(n)]
    meet = [Bool(f"meet_{i}") for i in range(n)]

    opt = Optimize()

    # Bounds and meeting constraints
    for i, p in enumerate(people):
        ws = p["window_start"]
        we = p["window_end"]
        dmin = p["min_duration"]
        opt.add(And(s[i] >= 0, s[i] <= 24*60, e[i] >= 0, e[i] <= 24*60))
        # If meeting, respect window and minimum duration; if not, times set to 0
        opt.add(Implies(meet[i], And(s[i] >= ws, e[i] <= we, e[i] - s[i] >= dmin)))
        opt.add(Implies(~meet[i], And(s[i] == 0, e[i] == 0)))

    # Non-overlap and travel feasibility between any two meetings
    for i in range(n):
        for j in range(i+1, n):
            li = people[i]["location"]
            lj = people[j]["location"]
            tij = t(li, lj)
            tji = t(lj, li)
            opt.add(Implies(And(meet[i], meet[j]),
                            Or(e[i] + tij <= s[j], e[j] + tji <= s[i])))

    # Ensure earliest scheduled meeting is reachable from Sunset at 9:00
    BIGM = 100000
    s_active = [If(meet[i], s[i], BIGM) for i in range(n)]
    # Compute min start among active meetings
    if n == 1:
        min_start = s_active[0]
    else:
        # Folded min using If
        min_start = s_active[0]
        for i in range(1, n):
            min_start = If(s_active[i] <= min_start, s_active[i], min_start)

    for i, p in enumerate(people):
        li = p["location"]
        opt.add(Implies(And(meet[i], s[i] == min_start),
                        s[i] >= arrive_time + t(SUNSET, li)))

    # Objectives:
    # 1) Maximize number of people met
    meet_count = sum([If(meet[i], 1, 0) for i in range(n)])
    opt.maximize(meet_count)

    # 2) Maximize total meeting time
    total_meet_minutes = sum([If(meet[i], e[i] - s[i], 0) for i in range(n)])
    opt.maximize(total_meet_minutes)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}, indent=2))
        return

    m = opt.model()

    # Build itinerary from model
    schedule = []
    for i, p in enumerate(people):
        if m.evaluate(meet[i], model_completion=True):
            start_min = m.evaluate(s[i]).as_long()
            end_min = m.evaluate(e[i]).as_long()
            schedule.append({
                "action": "meet",
                "location": p["location"],
                "person": p["name"],
                "start_min": start_min,
                "end_min": end_min
            })

    # Sort by start time
    schedule.sort(key=lambda x: x["start_min"])

    # Format times
    output = {"itinerary": []}
    for item in schedule:
        output["itinerary"].append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": time_to_str(item["start_min"]),
            "end_time": time_to_str(item["end_min"])
        })

    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()