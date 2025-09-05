import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Sum, Not

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Input parameters
    locations = ["North Beach", "Mission District", "The Castro"]
    travel = {
        ("North Beach", "Mission District"): 18,
        ("North Beach", "The Castro"): 22,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "The Castro"): 7,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Mission District"): 7,
    }

    start_location = "North Beach"
    arrival_time = 9 * 60  # 9:00

    # Friends and availability
    friends = {
        "James": {
            "location": "Mission District",
            "avail_start": 12 * 60 + 45,  # 12:45
            "avail_end": 14 * 60,         # 14:00
            "min_meet": 75
        },
        "Robert": {
            "location": "The Castro",
            "avail_start": 12 * 60 + 45,  # 12:45
            "avail_end": 15 * 60 + 15,    # 15:15
            "min_meet": 30
        }
    }

    # Z3 setup
    opt = Optimize()
    opt.set(priority='lex')

    # Variables
    sJ, eJ = Int('sJ'), Int('eJ')
    sR, eR = Int('sR'), Int('eR')
    meetJ, meetR = Bool('meetJ'), Bool('meetR')

    # Domain constraints (non-negative)
    for v in [sJ, eJ, sR, eR]:
        opt.add(v >= 0)

    # Availability constraints
    J = friends["James"]
    R = friends["Robert"]

    opt.add(Implies(meetJ, And(
        sJ >= J["avail_start"],
        eJ <= J["avail_end"],
        eJ - sJ >= J["min_meet"]
    )))
    opt.add(Implies(Not(meetJ), And(sJ == 0, eJ == 0)))

    opt.add(Implies(meetR, And(
        sR >= R["avail_start"],
        eR <= R["avail_end"],
        eR - sR >= R["min_meet"]
    )))
    opt.add(Implies(Not(meetR), And(sR == 0, eR == 0)))

    # Travel arrival times from start to first meeting
    nb_to_mission = travel[(start_location, "Mission District")]
    nb_to_castro = travel[(start_location, "The Castro")]
    mission_to_castro = travel[("Mission District", "The Castro")]
    castro_to_mission = travel[("The Castro", "Mission District")]

    # If only one meeting, ensure sufficient travel from start location
    opt.add(Implies(And(meetJ, Not(meetR)), sJ >= arrival_time + nb_to_mission))
    opt.add(Implies(And(meetR, Not(meetJ)), sR >= arrival_time + nb_to_castro))

    # If meeting both, enforce a valid order with travel and start from North Beach for the first one
    both = And(meetJ, meetR)
    j_before_r = And(
        sJ >= arrival_time + nb_to_mission,
        eJ + mission_to_castro <= sR
    )
    r_before_j = And(
        sR >= arrival_time + nb_to_castro,
        eR + castro_to_mission <= sJ
    )
    opt.add(Implies(both, Or(j_before_r, r_before_j)))

    # Objective 1: maximize number of friends met
    total_met = Sum(If(meetJ, 1, 0), If(meetR, 1, 0))
    opt.maximize(total_met)

    # Objective 2: maximize total meeting minutes (tie-breaker)
    total_minutes = Sum(If(meetJ, eJ - sJ, 0), If(meetR, eR - sR, 0))
    opt.maximize(total_minutes)

    # Solve
    if opt.check() != 1:  # sat
        print(json.dumps({"itinerary": []}))
        return
    m = opt.model()

    itinerary = []
    if m.evaluate(meetJ, model_completion=True):
        itinerary.append({
            "action": "meet",
            "location": J["location"],
            "person": "James",
            "start_time": minutes_to_str(m.evaluate(sJ).as_long()),
            "end_time": minutes_to_str(m.evaluate(eJ).as_long()),
        })
    if m.evaluate(meetR, model_completion=True):
        itinerary.append({
            "action": "meet",
            "location": R["location"],
            "person": "Robert",
            "start_time": minutes_to_str(m.evaluate(sR).as_long()),
            "end_time": minutes_to_str(m.evaluate(eR).as_long()),
        })

    # Sort by start time
    itinerary.sort(key=lambda x: (int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1])))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()