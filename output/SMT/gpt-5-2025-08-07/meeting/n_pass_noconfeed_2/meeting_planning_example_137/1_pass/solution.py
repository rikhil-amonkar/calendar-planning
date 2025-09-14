# SOLUTION:
import json
from z3 import Int, Bool, Optimize, Implies, And, Not, If, sat

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    # Locations
    FD = "Financial District"
    CT = "Chinatown"
    GGP = "Golden Gate Park"

    # Travel times in minutes
    travel = {
        (FD, CT): 5,
        (CT, FD): 5,
        (FD, GGP): 23,
        (GGP, FD): 26,
        (CT, GGP): 23,
        (GGP, CT): 23,
    }

    # Arrival at FD at 9:00 (in minutes from midnight)
    start_time_fd = 9 * 60  # 540

    # People and constraints
    people = {
        "Kenneth": {
            "location": CT,
            "window_start": 12 * 60,   # 12:00 -> 720
            "window_end": 15 * 60,     # 15:00 -> 900
            "min_duration": 90
        },
        "Barbara": {
            "location": GGP,
            "window_start": 8 * 60 + 15,  # 8:15 -> 495
            "window_end": 19 * 60,        # 19:00 -> 1140
            "min_duration": 45
        }
    }

    # Z3 variables
    s_K = Int('s_K')  # start time Kenneth
    s_B = Int('s_B')  # start time Barbara

    meet_K = Bool('meet_K')
    meet_B = Bool('meet_B')

    order_B_before_K = Bool('order_B_before_K')  # only relevant if both meet

    # Create optimizer
    o = Optimize()

    # Domain bounds (reasonable day bounds)
    o.add(s_K >= 0, s_K <= 24 * 60)
    o.add(s_B >= 0, s_B <= 24 * 60)

    # Meeting windows constraints (only apply if meeting that person)
    o.add(Implies(
        meet_K,
        And(
            s_K >= people["Kenneth"]["window_start"],
            s_K + people["Kenneth"]["min_duration"] <= people["Kenneth"]["window_end"]
        )
    ))
    o.add(Implies(
        meet_B,
        And(
            s_B >= people["Barbara"]["window_start"],
            s_B + people["Barbara"]["min_duration"] <= people["Barbara"]["window_end"]
        )
    ))

    # Start from FD travel constraints
    # If meeting only one person
    o.add(Implies(
        And(meet_B, Not(meet_K)),
        s_B >= start_time_fd + travel[(FD, GGP)]
    ))
    o.add(Implies(
        And(meet_K, Not(meet_B)),
        s_K >= start_time_fd + travel[(FD, CT)]
    ))

    # If meeting both, enforce one of the orders using the order boolean
    # Order: Barbara first then Kenneth
    o.add(Implies(
        And(meet_B, meet_K, order_B_before_K),
        And(
            s_B >= start_time_fd + travel[(FD, GGP)],
            s_K >= s_B + people["Barbara"]["min_duration"] + travel[(GGP, CT)]
        )
    ))
    # Order: Kenneth first then Barbara
    o.add(Implies(
        And(meet_B, meet_K, Not(order_B_before_K)),
        And(
            s_K >= start_time_fd + travel[(FD, CT)],
            s_B >= s_K + people["Kenneth"]["min_duration"] + travel[(CT, GGP)]
        )
    ))

    # Objective: maximize number of friends met
    total_meetings = If(meet_B, 1, 0) + If(meet_K, 1, 0)
    o.maximize(total_meetings)

    # Optional tie-breaker: minimize overall finish time if meeting both
    # Define end times for potential tie-breaking (not required, but helps pick earlier itinerary)
    e_K = s_K + people["Kenneth"]["min_duration"]
    e_B = s_B + people["Barbara"]["min_duration"]
    # Minimize the maximum end time among meetings that occur
    latest_end = Int('latest_end')
    o.add(latest_end >= 0)
    # latest_end >= each end if that meeting happens
    o.add(Implies(meet_K, latest_end >= e_K))
    o.add(Implies(meet_B, latest_end >= e_B))
    # If neither meeting happens, bound latest_end to 0
    o.add(Implies(And(Not(meet_K), Not(meet_B)), latest_end == 0))
    o.minimize(latest_end)

    # Solve
    if o.check() != sat:
        # In case of infeasible model (should not occur with given data)
        print(json.dumps({"itinerary": []}))
        return

    m = o.model()

    itinerary = []

    def add_event(person_key, start_var):
        person = people[person_key]
        start = m[start_var].as_long()
        end = start + person["min_duration"]
        itinerary.append({
            "action": "meet",
            "location": person["location"],
            "person": person_key,
            "start_time": minutes_to_str(start),
            "end_time": minutes_to_str(end)
        })

    if m[meet_B] and str(m[meet_B]) == "True":
        add_event("Barbara", s_B)
    if m[meet_K] and str(m[meet_K]) == "True":
        add_event("Kenneth", s_K)

    # Sort itinerary chronologically
    def time_key(item):
        h, mi = map(int, item["start_time"].split(":"))
        return h * 60 + mi

    itinerary.sort(key=time_key)

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()