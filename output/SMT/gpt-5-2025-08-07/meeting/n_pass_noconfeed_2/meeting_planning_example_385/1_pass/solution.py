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
    locations = ["Nob Hill", "Presidio", "North Beach", "Fisherman's Wharf", "Pacific Heights"]

    # Directed travel times (in minutes)
    travel = {
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "Pacific Heights"): 8,

        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Pacific Heights"): 11,

        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Pacific Heights"): 8,

        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Pacific Heights"): 12,

        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
    }

    # Start state
    start_location = "Nob Hill"
    day_start = minutes(9, 0)

    # People data: name -> (location, window_start, window_end, min_duration)
    people = {
        "Jeffrey": ("Presidio", minutes(8, 0), minutes(10, 0), 105),
        "Steven": ("North Beach", minutes(13, 30), minutes(22, 0), 45),
        "Barbara": ("Fisherman's Wharf", minutes(18, 0), minutes(21, 30), 30),
        "John": ("Pacific Heights", minutes(9, 0), minutes(13, 30), 15),
    }

    # Z3 variables
    opt = Optimize()

    starts = {}
    ends = {}
    durs = {}
    attends = {}

    for person, (loc, wstart, wend, mindur) in people.items():
        s = Int(f"{person}_start")
        e = Int(f"{person}_end")
        d = Int(f"{person}_dur")
        a = Bool(f"{person}_attend")

        starts[person] = s
        ends[person] = e
        durs[person] = d
        attends[person] = a

        # Domains
        opt.add(s >= 0, s <= 24*60)
        opt.add(e >= 0, e <= 24*60)
        opt.add(d >= 0)
        opt.add(e == s + d)

        # If attending, enforce window, min duration, and reachability from start location
        # Reachability: start time must be no earlier than earliest arrival from starting point
        earliest_arrival = day_start + travel[(start_location, loc)]
        opt.add(If(a,
                   And(s >= wstart, e <= wend, d >= mindur, s >= earliest_arrival),
                   And(d == 0, e == s)
                   ))

    # Non-overlap and travel constraints between meetings
    persons = list(people.keys())
    for i in range(len(persons)):
        for j in range(i+1, len(persons)):
            pi = persons[i]
            pj = persons[j]
            li = people[pi][0]
            lj = people[pj][0]
            tij = travel[(li, lj)]
            tji = travel[(lj, li)]
            # If both meetings are attended, enforce disjunctive ordering with travel times
            opt.add(Implies(And(attends[pi], attends[pj]),
                            Or(ends[pi] + tij <= starts[pj],
                               ends[pj] + tji <= starts[pi])))

    # Objective: maximize the number of friends met (who satisfy their minimum durations)
    total_met = Sum([If(attends[p], 1, 0) for p in persons])
    opt.maximize(total_met)

    # Optional tie-breakers: minimize total idle time or latest end (not required). Keep simple.

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    # Extract attended meetings
    itinerary = []
    for person in persons:
        if is_true(model[attends[person]]):
            s = model[starts[person]].as_long()
            e = model[ends[person]].as_long()
            loc = people[person][0]
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": person,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e)
            })

    # Sort by start times
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()