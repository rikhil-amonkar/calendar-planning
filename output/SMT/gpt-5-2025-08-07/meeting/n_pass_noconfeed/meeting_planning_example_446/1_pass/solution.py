"SOLUTION:"
import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def parse_time(tstr):
    # format 'H:MM'
    parts = tstr.split(':')
    return minutes(int(parts[0]), int(parts[1]))

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def build_solver():
    # Locations
    RICH = "Richmond District"
    MAR = "Marina District"
    CHI = "Chinatown"
    FIN = "Financial District"
    BAY = "Bayview"
    UNI = "Union Square"
    locations = [RICH, MAR, CHI, FIN, BAY, UNI]

    # Travel distances (minutes)
    dist = {loc: {} for loc in locations}
    dist[RICH][MAR] = 9
    dist[RICH][CHI] = 20
    dist[RICH][FIN] = 22
    dist[RICH][BAY] = 26
    dist[RICH][UNI] = 21

    dist[MAR][RICH] = 11
    dist[MAR][CHI] = 16
    dist[MAR][FIN] = 17
    dist[MAR][BAY] = 27
    dist[MAR][UNI] = 16

    dist[CHI][RICH] = 20
    dist[CHI][MAR] = 12
    dist[CHI][FIN] = 5
    dist[CHI][BAY] = 22
    dist[CHI][UNI] = 7

    dist[FIN][RICH] = 21
    dist[FIN][MAR] = 15
    dist[FIN][CHI] = 5
    dist[FIN][BAY] = 19
    dist[FIN][UNI] = 9

    dist[BAY][RICH] = 25
    dist[BAY][MAR] = 25
    dist[BAY][CHI] = 18
    dist[BAY][FIN] = 19
    dist[BAY][UNI] = 17

    dist[UNI][RICH] = 20
    dist[UNI][MAR] = 18
    dist[UNI][CHI] = 7
    dist[UNI][FIN] = 9
    dist[UNI][BAY] = 15

    # Meeting constraints
    # person: location, availability start, availability end, min duration
    people = {
        "Kimberly": {
            "location": MAR,
            "avail_start": minutes(13, 15),
            "avail_end": minutes(16, 45),
            "min_duration": 15
        },
        "Robert": {
            "location": CHI,
            "avail_start": minutes(12, 15),
            "avail_end": minutes(20, 15),
            "min_duration": 15
        },
        "Rebecca": {
            "location": FIN,
            "avail_start": minutes(13, 15),
            "avail_end": minutes(16, 45),
            "min_duration": 75
        },
        "Margaret": {
            "location": BAY,
            "avail_start": minutes(9, 30),
            "avail_end": minutes(13, 30),
            "min_duration": 30
        },
        "Kenneth": {
            "location": UNI,
            "avail_start": minutes(19, 30),
            "avail_end": minutes(21, 15),
            "min_duration": 75
        }
    }

    start_city = RICH
    start_time = minutes(9, 0)

    # Z3 Variables
    s = Optimize()
    s.set(priority='lex')

    vars = {}
    all_names = list(people.keys())
    for name in all_names:
        vars[name] = {
            "start": Int(f"start_{name}"),
            "end": Int(f"end_{name}"),
            "meet": Bool(f"meet_{name}")
        }
        st = vars[name]["start"]
        en = vars[name]["end"]
        meet = vars[name]["meet"]
        avail_start = people[name]["avail_start"]
        avail_end = people[name]["avail_end"]
        min_dur = people[name]["min_duration"]

        # Bounds
        s.add(st >= 0, st <= 24 * 60)
        s.add(en >= 0, en <= 24 * 60)
        s.add(en >= st)

        # If meeting occurs, enforce availability and duration
        s.add(Implies(meet, And(st >= avail_start,
                                en <= avail_end,
                                en - st >= min_dur)))
        # If no meeting, zero duration
        s.add(Implies(Not(meet), en == st))

    # Pairwise non-overlap with travel time
    for i in range(len(all_names)):
        for j in range(i + 1, len(all_names)):
            ni = all_names[i]
            nj = all_names[j]
            li = people[ni]["location"]
            lj = people[nj]["location"]
            si = vars[ni]["start"]
            ei = vars[ni]["end"]
            sj = vars[nj]["start"]
            ej = vars[nj]["end"]
            mi = vars[ni]["meet"]
            mj = vars[nj]["meet"]
            # If both meetings occur, enforce sequencing with travel times
            s.add(Implies(And(mi, mj),
                          Or(ei + dist[li][lj] <= sj,
                             ej + dist[lj][li] <= si)))

    # Anchor to start city/time using a dummy "start node"
    for name in all_names:
        meet = vars[name]["meet"]
        st = vars[name]["start"]
        en = vars[name]["end"]
        loc = people[name]["location"]
        # Either end before start_time after returning to start (impossible), or reachable from start
        s.add(Implies(meet,
                      Or(en + dist[loc][start_city] <= start_time,
                         start_time + dist[start_city][loc] <= st)))

    # Objective 1: maximize number of people met
    meet_count = Sum([If(vars[name]["meet"], 1, 0) for name in all_names])
    s.maximize(meet_count)

    # Objective 2: maximize total meeting time
    total_time = Sum([vars[name]["end"] - vars[name]["start"] for name in all_names])
    s.maximize(total_time)

    return s, vars, people

def extract_itinerary(model, vars, people):
    itinerary = []
    for name, v in vars.items():
        meet_val = is_true(model[v["meet"]])
        if meet_val:
            st = model[v["start"]].as_long()
            en = model[v["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "location": people[name]["location"],
                "person": name,
                "start_time": minutes_to_str(st),
                "end_time": minutes_to_str(en)
            })
    itinerary.sort(key=lambda x: parse_time(x["start_time"]))
    return itinerary

def main():
    s, vars, people = build_solver()
    if s.check() != sat:
        print(json.dumps({"itinerary": []}, indent=2))
        return
    model = s.model()
    itinerary = extract_itinerary(model, vars, people)
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()