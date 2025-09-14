import json
from z3 import *

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Constants
    DAY_START = 9 * 60  # 9:00
    START_LOC = "Sunset District"

    # People and their availability/requirements
    people = [
        {"name": "Sarah",   "loc": "North Beach",  "avail_start": 16*60, "avail_end": 18*60+15, "min_duration": 60},
        {"name": "Jeffrey", "loc": "Union Square", "avail_start": 15*60, "avail_end": 22*60,    "min_duration": 75},
        {"name": "Brian",   "loc": "Alamo Square", "avail_start": 16*60, "avail_end": 17*60+30, "min_duration": 75},
    ]

    # Travel times (in minutes)
    travel = {
        ("Sunset District", "North Beach"): 29,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Alamo Square"): 17,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Alamo Square"): 16,
        ("Union Square", "Sunset District"): 26,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Alamo Square"): 15,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Union Square"): 14,
    }

    def tt(frm, to):
        return travel[(frm, to)]

    opt = Optimize()
    opt.set(priority='lex')

    n = len(people)

    # Variables per person
    meet = [Bool(f"meet_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    dur = [Int(f"dur_{i}") for i in range(n)]

    # Basic domains
    for i, p in enumerate(people):
        opt.add(start[i] >= 0, end[i] >= 0, dur[i] >= 0)

        # If meeting, respect availability and minimum duration
        opt.add(Implies(meet[i],
                        And(
                            start[i] >= p["avail_start"],
                            end[i]   <= p["avail_end"],
                            end[i]   == start[i] + dur[i],
                            dur[i]   >= p["min_duration"]
                        )))
        # If not meeting, collapse variables to 0 to avoid accidental ordering influences
        opt.add(Implies(Not(meet[i]), And(start[i] == 0, end[i] == 0, dur[i] == 0)))

        # Must be reachable from starting location at 9:00
        opt.add(Implies(meet[i], start[i] >= DAY_START + tt(START_LOC, p["loc"])))

    # Disjunctive scheduling with travel/setup times between meetings
    for i in range(n):
        for j in range(i+1, n):
            li = people[i]["loc"]
            lj = people[j]["loc"]
            opt.add(Implies(And(meet[i], meet[j]),
                            Or(start[i] >= end[j] + tt(lj, li),
                               start[j] >= end[i] + tt(li, lj))))

    # Last end time (to minimize makespan as tie-breaker)
    last_end = Int("last_end")
    opt.add(last_end >= DAY_START)
    # last_end must be at least every met end
    for i in range(n):
        opt.add(Implies(meet[i], last_end >= end[i]))

    # Objectives:
    # 1) Maximize number of friends met
    total_met = Sum([If(meet[i], 1, 0) for i in range(n)])
    opt.maximize(total_met)
    # 2) Minimize the end time of the day
    opt.minimize(last_end)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}, indent=2))
        return
    m = opt.model()

    # Build itinerary (only meetings actually scheduled), sorted by start time
    meetings = []
    for i, p in enumerate(people):
        if is_true(m.evaluate(meet[i])):
            st = m.evaluate(start[i]).as_long()
            en = m.evaluate(end[i]).as_long()
            meetings.append({
                "action": "meet",
                "location": p["loc"],
                "person": p["name"],
                "start_time": minutes_to_str(st),
                "end_time": minutes_to_str(en)
            })

    meetings.sort(key=lambda x: (int(x["start_time"].split(':')[0])*60 + int(x["start_time"].split(':')[1])))

    result = {"itinerary": meetings}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    # The script must start with 'SOLUTION:' as per instructions
    print("SOLUTION:")
    main()