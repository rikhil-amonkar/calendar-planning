import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum, sat

def m2str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Locations
    SUNSET = "Sunset District"
    RUSSIAN = "Russian Hill"
    CHINATOWN = "Chinatown"
    PRESIDIO = "Presidio"
    WHARF = "Fisherman's Wharf"

    # Travel times (minutes), directional as given
    travel = {
        (SUNSET, RUSSIAN): 24,
        (SUNSET, CHINATOWN): 30,
        (SUNSET, PRESIDIO): 16,
        (SUNSET, WHARF): 29,

        (RUSSIAN, SUNSET): 23,
        (RUSSIAN, CHINATOWN): 9,
        (RUSSIAN, PRESIDIO): 14,
        (RUSSIAN, WHARF): 7,

        (CHINATOWN, SUNSET): 29,
        (CHINATOWN, RUSSIAN): 7,
        (CHINATOWN, PRESIDIO): 19,
        (CHINATOWN, WHARF): 8,

        (PRESIDIO, SUNSET): 15,
        (PRESIDIO, RUSSIAN): 14,
        (PRESIDIO, CHINATOWN): 21,
        (PRESIDIO, WHARF): 19,

        (WHARF, SUNSET): 27,
        (WHARF, RUSSIAN): 7,
        (WHARF, CHINATOWN): 12,
        (WHARF, PRESIDIO): 17,
    }

    def t(frm, to):
        if frm == to:
            return 0
        return travel[(frm, to)]

    # Minutes since midnight for key times
    def hhmm(h, m):
        return h * 60 + m

    ARRIVAL_START = hhmm(9, 0)  # 9:00 at Sunset District

    # Friends and constraints
    friends = [
        {
            "name": "William",
            "location": RUSSIAN,
            "window_start": hhmm(18, 30),
            "window_end": hhmm(20, 45),
            "min_duration": 105
        },
        {
            "name": "Michelle",
            "location": CHINATOWN,
            "window_start": hhmm(8, 15),
            "window_end": hhmm(14, 0),
            "min_duration": 15
        },
        {
            "name": "George",
            "location": PRESIDIO,
            "window_start": hhmm(10, 30),
            "window_end": hhmm(18, 45),
            "min_duration": 30
        },
        {
            "name": "Robert",
            "location": WHARF,
            "window_start": hhmm(9, 0),
            "window_end": hhmm(13, 45),
            "min_duration": 30
        },
    ]

    n = len(friends)

    # Z3 variables
    meet = [Bool(f"meet_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    dur = [Int(f"dur_{i}") for i in range(n)]

    o = Optimize()
    o.set(priority='lex')

    DAY_MAX = hhmm(23, 59)

    for i, f in enumerate(friends):
        ws = f["window_start"]
        we = f["window_end"]
        mind = f["min_duration"]
        # Domain bounds
        o.add(start[i] >= 0, start[i] <= DAY_MAX + 1)
        o.add(end[i] >= 0, end[i] <= DAY_MAX + 1)
        o.add(dur[i] >= 0)

        # Meeting implies window and duration constraints
        o.add(Implies(meet[i], And(
            start[i] >= ws,
            end[i] <= we,
            dur[i] >= mind,
            end[i] == start[i] + dur[i],
            # Reachability from initial location at 9:00
            start[i] >= ARRIVAL_START + t(SUNSET, f["location"])
        )))
        # If not meeting, set zero-duration dummy times (to keep model tight)
        o.add(Implies(Or(meet[i] == False), And(
            dur[i] == 0,
            start[i] == ws,
            end[i] == ws
        )))

    # Non-overlap with travel: if both meetings occur, enforce ordering with travel times
    for i in range(n):
        for j in range(i + 1, n):
            li = friends[i]["location"]
            lj = friends[j]["location"]
            o.add(Implies(And(meet[i], meet[j]),
                          Or(end[i] + t(li, lj) <= start[j],
                             end[j] + t(lj, li) <= start[i])))

    # Objectives:
    meet_count = Sum([If(meet[i], 1, 0) for i in range(n)])
    total_meet_time = Sum([dur[i] for i in range(n)])

    o.maximize(meet_count)
    o.maximize(total_meet_time)

    if o.check() != sat:
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    m = o.model()

    itinerary = []
    for i, f in enumerate(friends):
        if m.evaluate(meet[i], model_completion=True):
            s = m.evaluate(start[i], model_completion=True).as_long()
            e = m.evaluate(end[i], model_completion=True).as_long()
            itinerary.append({
                "action": "meet",
                "location": f["location"],
                "person": f["name"],
                "start_time": m2str(s),
                "end_time": m2str(e)
            })

    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()