import json
from z3 import *

def fmt_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Time constants (minutes since midnight)
    NINE_AM = 9 * 60
    START_LOC = "Nob Hill"

    # Travel times (minutes)
    travel = {
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Mission District"): 13,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Mission District"): 15,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Pacific Heights"): 16
    }

    # Availabilities and minimums
    # Kenneth at Mission District
    K_location = "Mission District"
    K_name = "Kenneth"
    K_start = 12 * 60        # 12:00
    K_end = 15 * 60 + 45     # 15:45
    K_min = 45

    # Thomas at Pacific Heights
    T_location = "Pacific Heights"
    T_name = "Thomas"
    T_start = 15 * 60 + 30   # 15:30
    T_end = 19 * 60 + 15     # 19:15
    T_min = 75

    # Create optimizer
    opt = Optimize()

    # Variables
    sK = Int("sK")  # start Kenneth
    eK = Int("eK")  # end Kenneth
    sT = Int("sT")  # start Thomas
    eT = Int("eT")  # end Thomas

    mK = Int("mK")  # 0/1 meet Kenneth
    mT = Int("mT")  # 0/1 meet Thomas

    ordKT = Int("ordKT")  # 0 = K before T, 1 = T before K

    # Domains
    for v in [sK, eK, sT, eT]:
        opt.add(v >= 0, v <= 24 * 60)
    opt.add(mK >= 0, mK <= 1)
    opt.add(mT >= 0, mT <= 1)
    opt.add(ordKT >= 0, ordKT <= 1)

    # Meeting window constraints
    opt.add(Implies(mK == 1, And(sK >= K_start, eK <= K_end, eK - sK >= K_min, sK < eK)))
    opt.add(Implies(mT == 1, And(sT >= T_start, eT <= T_end, eT - sT >= T_min, sT < eT)))

    # From starting location at 9:00 at Nob Hill
    # Single meeting cases
    opt.add(Implies(And(mK == 1, mT == 0), sK >= NINE_AM + travel[(START_LOC, K_location)]))
    opt.add(Implies(And(mT == 1, mK == 0), sT >= NINE_AM + travel[(START_LOC, T_location)]))

    # Both meetings: order and travel constraints
    # K then T
    opt.add(Implies(And(mK == 1, mT == 1, ordKT == 0),
                    And(sK >= NINE_AM + travel[(START_LOC, K_location)],
                        sT >= eK + travel[(K_location, T_location)])))
    # T then K
    opt.add(Implies(And(mK == 1, mT == 1, ordKT == 1),
                    And(sT >= NINE_AM + travel[(START_LOC, T_location)],
                        sK >= eT + travel[(T_location, K_location)])))

    # Objective 1: maximize number of meetings
    h1 = opt.maximize(mK + mT)

    # Objective 2: maximize total meeting time
    durK = eK - sK
    durT = eT - sT
    total_dur = If(mK == 1, durK, 0) + If(mT == 1, durT, 0)
    h2 = opt.maximize(total_dur)

    # Objective 3: tie-breaker, minimize Thomas start time if meeting him (prefers earlier T start)
    h3 = opt.minimize(If(mT == 1, sT, 24 * 60))

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    meet_K = model.eval(mK).as_long()
    meet_T = model.eval(mT).as_long()

    itinerary = []

    if meet_K == 1:
        sK_val = model.eval(sK).as_long()
        eK_val = model.eval(eK).as_long()
        itinerary.append({
            "action": "meet",
            "location": K_location,
            "person": K_name,
            "start_time": fmt_time(sK_val),
            "end_time": fmt_time(eK_val)
        })

    if meet_T == 1:
        sT_val = model.eval(sT).as_long()
        eT_val = model.eval(eT).as_long()
        itinerary.append({
            "action": "meet",
            "location": T_location,
            "person": T_name,
            "start_time": fmt_time(sT_val),
            "end_time": fmt_time(eT_val)
        })

    # Sort itinerary by start_time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()