import json
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def solve_schedule():
    # Locations
    NB = "North Beach"
    PH = "Pacific Heights"
    E = "Embarcadero"

    # Travel times (minutes), directed
    travel = {
        (NB, PH): 8,
        (NB, E): 6,
        (PH, NB): 9,
        (PH, E): 10,
        (E, NB): 5,
        (E, PH): 11,
    }

    # Arrival at North Beach at 9:00
    start_time = minutes(9, 0)

    # Friend availability windows and minimum durations
    # Karen at Pacific Heights: 18:45 - 20:15 (min 90)
    K_loc = PH
    K_start = minutes(18, 45)
    K_end = minutes(20, 15)
    K_min = 90

    # Mark at Embarcadero: 13:00 - 17:45 (min 120)
    M_loc = E
    M_start = minutes(13, 0)
    M_end = minutes(17, 45)
    M_min = 120

    # Z3 variables
    s_K, e_K = Int('s_K'), Int('e_K')
    s_M, e_M = Int('s_M'), Int('e_M')
    meet_K, meet_M = Bool('meet_K'), Bool('meet_M')
    order_EP = Bool('order_EP')  # True: Embarcadero then Pacific Heights; False: Pacific Heights then Embarcadero

    o = Optimize()

    # Bounds for times
    for v in [s_K, e_K, s_M, e_M]:
        o.add(v >= 0, v <= 24 * 60)

    # Meeting window and duration constraints
    o.add(Implies(meet_K, And(s_K >= K_start, e_K <= K_end, e_K - s_K >= K_min)))
    o.add(Implies(meet_M, And(s_M >= M_start, e_M <= M_end, e_M - s_M >= M_min)))

    # Arrival to first meeting constraints from North Beach
    o.add(Implies(And(meet_M, Not(meet_K)), s_M >= start_time + travel[(NB, M_loc)]))
    o.add(Implies(And(meet_K, Not(meet_M)), s_K >= start_time + travel[(NB, K_loc)]))
    o.add(Implies(And(meet_M, meet_K, order_EP), s_M >= start_time + travel[(NB, M_loc)]))
    o.add(Implies(And(meet_M, meet_K, Not(order_EP)), s_K >= start_time + travel[(NB, K_loc)]))

    # Sequencing and travel between meetings if meeting both
    o.add(Implies(And(meet_M, meet_K, order_EP), s_K >= e_M + travel[(M_loc, K_loc)]))
    o.add(Implies(And(meet_M, meet_K, Not(order_EP)), s_M >= e_K + travel[(K_loc, M_loc)]))

    # Define travel total expression for optimization (sum of traversed legs)
    NB_to_E = travel[(NB, E)]
    NB_to_PH = travel[(NB, PH)]
    E_to_PH = travel[(E, PH)]
    PH_to_E = travel[(PH, E)]

    travel_total = If(And(meet_M, meet_K, order_EP),
                      NB_to_E + E_to_PH,
                      If(And(meet_M, meet_K, Not(order_EP)),
                         NB_to_PH + PH_to_E,
                         If(And(meet_M, Not(meet_K)),
                            NB_to_E,
                            If(And(meet_K, Not(meet_M)),
                               NB_to_PH,
                               0))))

    # Objectives:
    # 1) Maximize number of friends met
    friends_met = If(meet_M, 1, 0) + If(meet_K, 1, 0)
    o.maximize(friends_met)
    # 2) Maximize total meeting duration
    total_meet_minutes = If(meet_M, e_M - s_M, 0) + If(meet_K, e_K - s_K, 0)
    o.maximize(total_meet_minutes)
    # 3) Minimize total travel time
    o.minimize(travel_total)

    # Solve
    if o.check() != sat:
        # If unsat, output empty itinerary
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    m = o.model()

    itinerary = []

    def add_meeting(person, location, s_var, e_var, meet_var):
        if is_true(m[meet_var]):
            s = m[s_var].as_long()
            e = m[e_var].as_long()
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": fmt_time(s),
                "end_time": fmt_time(e)
            })

    add_meeting("Mark", E, s_M, e_M, meet_M)
    add_meeting("Karen", PH, s_K, e_K, meet_K)

    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    solve_schedule()