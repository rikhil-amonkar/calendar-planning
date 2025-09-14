import json
from z3 import Optimize, Int

def minutes(h, m):
    return h * 60 + m

def fmt_time(total_min):
    h = total_min // 60
    m = total_min % 60
    return f"{h}:{m:02d}"

def plan_schedule():
    # Input parameters (can be adjusted as needed)
    params = {
        "start_location": "Nob Hill",
        "start_time": minutes(9, 0),  # 9:00
        "people": [
            {
                "name": "Robert",
                "location": "Presidio",
                "avail_start": minutes(11, 15),  # 11:15
                "avail_end": minutes(17, 45),    # 17:45
                "min_meet": 120
            }
        ],
        "travel_minutes": {
            ("Nob Hill", "Presidio"): 17,
            ("Presidio", "Nob Hill"): 18
        }
    }

    # Extract parameters for Robert (single friend scenario)
    start_loc = params["start_location"]
    day_start_time = params["start_time"]
    robert = params["people"][0]
    robert_loc = robert["location"]
    robert_name = robert["name"]
    r_start = robert["avail_start"]
    r_end = robert["avail_end"]
    min_meet = robert["min_meet"]
    travel_np = params["travel_minutes"][(start_loc, robert_loc)]

    # Z3 variables
    dep = Int("depart_NobHill_to_Presidio")          # departure time from Nob Hill
    arr = Int("arrive_Presidio")                     # arrival time at Presidio
    meet_start = Int("meet_start_Robert_Presidio")   # meeting start at Presidio
    meet_end = Int("meet_end_Robert_Presidio")       # meeting end at Presidio
    wait = Int("wait_before_meeting")                # waiting time at Presidio before meeting

    opt = Optimize()

    # Domain constraints: times within a day
    for v in [dep, arr, meet_start, meet_end, wait]:
        opt.add(v >= 0, v <= 24 * 60)

    # Travel and meeting feasibility constraints
    opt.add(dep >= day_start_time)                   # can't depart before arriving at Nob Hill at 9:00
    opt.add(arr == dep + travel_np)                  # arrival respects travel time
    opt.add(meet_start >= arr)                       # can't start meeting before arrival
    opt.add(meet_start >= r_start)                   # can't start before Robert is available
    opt.add(meet_end <= r_end)                       # can't end after Robert leaves
    opt.add(meet_end > meet_start)                   # positive meeting duration
    opt.add(meet_end - meet_start >= min_meet)       # minimum desired meeting time
    opt.add(wait == meet_start - arr)                # define waiting time
    opt.add(wait >= 0)                               # can't have negative wait

    # Objectives:
    # 1) Maximize meeting duration
    opt.maximize(meet_end - meet_start)
    # 2) Minimize waiting time (arrive just in time if possible)
    opt.minimize(wait)
    # 3) Among ties, maximize the end time (push as late as possible)
    opt.maximize(meet_end)

    if opt.check() != 1:  # not sat or unknown
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    model = opt.model()
    ms = model[meet_start].as_long()
    me = model[meet_end].as_long()

    itinerary = [
        {
            "action": "meet",
            "location": robert_loc,
            "person": robert_name,
            "start_time": fmt_time(ms),
            "end_time": fmt_time(me)
        }
    ]

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    plan_schedule()