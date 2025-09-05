from z3 import Optimize, Int, Bool, BoolVal, If, And, Or, Implies, sat, is_true
import json

def time_to_minutes(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    SUNSET = "Sunset District"
    NORTH_BEACH = "North Beach"
    UNION_SQUARE = "Union Square"
    ALAMO_SQUARE = "Alamo Square"

    # Travel times (directed, in minutes)
    travel = {
        SUNSET: {
            NORTH_BEACH: 29,
            UNION_SQUARE: 30,
            ALAMO_SQUARE: 17
        },
        NORTH_BEACH: {
            SUNSET: 27,
            UNION_SQUARE: 7,
            ALAMO_SQUARE: 16
        },
        UNION_SQUARE: {
            SUNSET: 26,
            NORTH_BEACH: 10,
            ALAMO_SQUARE: 15
        },
        ALAMO_SQUARE: {
            SUNSET: 16,
            NORTH_BEACH: 15,
            UNION_SQUARE: 14
        }
    }

    # Day start
    arrival_time = time_to_minutes(9, 0)  # 9:00 at Sunset District

    # People availability and requirements
    people = {
        "Sarah": {
            "location": NORTH_BEACH,
            "start": time_to_minutes(16, 0),     # 16:00
            "end": time_to_minutes(18, 15),      # 18:15
            "min_dur": 60
        },
        "Jeffrey": {
            "location": UNION_SQUARE,
            "start": time_to_minutes(15, 0),     # 15:00
            "end": time_to_minutes(22, 0),       # 22:00
            "min_dur": 75
        },
        "Brian": {
            "location": ALAMO_SQUARE,
            "start": time_to_minutes(16, 0),     # 16:00
            "end": time_to_minutes(17, 30),      # 17:30
            "min_dur": 75
        }
    }

    # Z3 Optimize solver with lexicographic priority (maximize number of meetings, then total meeting time)
    opt = Optimize()
    opt.set(priority='lex')

    # Variables per person
    start_vars = {}
    end_vars = {}
    met_vars = {}
    for name, info in people.items():
        start_vars[name] = Int(f"start_{name}")
        end_vars[name] = Int(f"end_{name}")
        met_vars[name] = Bool(f"met_{name}")

        a_start = info["start"]
        a_end = info["end"]
        min_dur = info["min_dur"]

        # Time bounds within availability window
        opt.add(start_vars[name] >= a_start)
        opt.add(end_vars[name] <= a_end)
        opt.add(end_vars[name] >= start_vars[name])

        # Meeting duration constraints contingent on meeting decision
        opt.add(Implies(met_vars[name], end_vars[name] - start_vars[name] >= min_dur))
        # If not meeting, force zero duration to avoid accidental contributions to objectives
        opt.add(Implies(~met_vars[name], end_vars[name] == start_vars[name]))

        # Sanity bounds within day
        opt.add(start_vars[name] >= 0, end_vars[name] >= 0)
        opt.add(start_vars[name] <= time_to_minutes(23, 59),
                end_vars[name] <= time_to_minutes(23, 59))

    # Add a dummy START node to model initial position and travel from arrival
    START = "START"
    start_vars[START] = Int("start_START")
    end_vars[START] = Int("end_START")
    met_vars[START] = BoolVal(True)  # always active
    opt.add(start_vars[START] == arrival_time)
    opt.add(end_vars[START] == arrival_time)
    start_location = SUNSET

    # Ordering and travel-time constraints between all pairs (including START)
    all_nodes = [START] + list(people.keys())

    def loc_of(node):
        if node == START:
            return start_location
        return people[node]["location"]

    for i in range(len(all_nodes)):
        for j in range(i + 1, len(all_nodes)):
            ni = all_nodes[i]
            nj = all_nodes[j]
            li = loc_of(ni)
            lj = loc_of(nj)
            # Travel time between nodes
            tij = travel[li][lj] if li in travel and lj in travel[li] else 0
            tji = travel[lj][li] if lj in travel and li in travel[lj] else 0

            # If both nodes are active (met), enforce non-overlap with travel
            opt.add(Implies(And(met_vars[ni], met_vars[nj]),
                            Or(end_vars[ni] + tij <= start_vars[nj],
                               end_vars[nj] + tji <= start_vars[ni])))

    # Objective 1: maximize number of distinct friends met (exclude START)
    meet_count = sum([If(met_vars[name], 1, 0) for name in people.keys()])
    opt.maximize(meet_count)

    # Objective 2: maximize total meeting time (exclude START)
    total_meeting_time = sum([If(met_vars[name], end_vars[name] - start_vars[name], 0) for name in people.keys()])
    opt.maximize(total_meeting_time)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}, indent=2))
        return

    m = opt.model()

    # Collect meetings decided as True
    meetings = []
    for name in people.keys():
        if is_true(m.evaluate(met_vars[name], model_completion=True)):
            s = m.evaluate(start_vars[name]).as_long()
            e = m.evaluate(end_vars[name]).as_long()
            meetings.append({
                "person": name,
                "location": people[name]["location"],
                "start": s,
                "end": e
            })

    # Sort by start time
    meetings.sort(key=lambda x: x["start"])

    # Build JSON output
    itinerary = []
    for mt in meetings:
        itinerary.append({
            "action": "meet",
            "location": mt["location"],
            "person": mt["person"],
            "start_time": minutes_to_str(mt["start"]),
            "end_time": minutes_to_str(mt["end"])
        })

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()