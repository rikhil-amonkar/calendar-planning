import json
from z3 import Optimize, Int, Bool, Implies, And, Or, If, is_true, Not, sat

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Travel times in minutes
    travel = {
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Mission District"): 13,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Mission District"): 15,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Pacific Heights"): 16,
    }

    # Locations
    NH = "Nob Hill"
    PH = "Pacific Heights"
    MD = "Mission District"

    # Arrival time at Nob Hill (minutes since midnight)
    arrive_NH = 9 * 60  # 9:00

    # Friend availability windows and minimum meeting durations
    # Thomas at Pacific Heights from 15:30 to 19:15, min 75 minutes
    thomas_loc = PH
    thomas_start = 15 * 60 + 30  # 930
    thomas_end = 19 * 60 + 15    # 1155
    thomas_min = 75

    # Kenneth at Mission District from 12:00 to 15:45, min 45 minutes
    kenneth_loc = MD
    kenneth_start = 12 * 60      # 720
    kenneth_end = 15 * 60 + 45   # 945
    kenneth_min = 45

    # Z3 variables
    opt = Optimize()
    opt.set(priority='lex')  # prioritize objectives in order

    s_T = Int('s_T')  # Thomas start
    e_T = Int('e_T')  # Thomas end
    s_K = Int('s_K')  # Kenneth start
    e_K = Int('e_K')  # Kenneth end

    attend_T = Bool('attend_T')
    attend_K = Bool('attend_K')

    # Basic domains
    opt.add(s_T >= 0, e_T >= 0, s_K >= 0, e_K >= 0)

    # Meeting window and minimum duration constraints
    opt.add(Implies(attend_T, And(s_T >= thomas_start, e_T <= thomas_end, e_T - s_T >= thomas_min)))
    opt.add(Implies(attend_K, And(s_K >= kenneth_start, e_K <= kenneth_end, e_K - s_K >= kenneth_min)))

    # Travel feasibility constraints from starting location for single-meeting scenarios
    opt.add(Implies(And(attend_T, Not(attend_K)), s_T >= arrive_NH + travel[(NH, thomas_loc)]))
    opt.add(Implies(And(attend_K, Not(attend_T)), s_K >= arrive_NH + travel[(NH, kenneth_loc)]))

    # If meeting both, enforce a feasible order with travel time between locations,
    # and ensure the first meeting is reachable from the starting point.
    opt.add(Implies(
        And(attend_T, attend_K),
        Or(
            And(
                e_T + travel[(thomas_loc, kenneth_loc)] <= s_K,
                s_T >= arrive_NH + travel[(NH, thomas_loc)]
            ),
            And(
                e_K + travel[(kenneth_loc, thomas_loc)] <= s_T,
                s_K >= arrive_NH + travel[(NH, kenneth_loc)]
            )
        )
    ))

    # Optimization goals
    num_meet = If(attend_T, 1, 0) + If(attend_K, 1, 0)
    total_minutes = If(attend_T, e_T - s_T, 0) + If(attend_K, e_K - s_K, 0)

    opt.maximize(num_meet)
    opt.maximize(total_minutes)

    # Solve
    if opt.check() != sat:
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    m = opt.model()

    itinerary = []

    # Collect meetings if attended
    if is_true(m.evaluate(attend_K, model_completion=True)):
        k_start = m.evaluate(s_K).as_long()
        k_end = m.evaluate(e_K).as_long()
        itinerary.append({
            "action": "meet",
            "location": "Mission District",
            "person": "Kenneth",
            "start_time": minutes_to_str(k_start),
            "end_time": minutes_to_str(k_end)
        })

    if is_true(m.evaluate(attend_T, model_completion=True)):
        t_start = m.evaluate(s_T).as_long()
        t_end = m.evaluate(e_T).as_long()
        itinerary.append({
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Thomas",
            "start_time": minutes_to_str(t_start),
            "end_time": minutes_to_str(t_end)
        })

    # Sort itinerary by start_time to ensure chronological order
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()