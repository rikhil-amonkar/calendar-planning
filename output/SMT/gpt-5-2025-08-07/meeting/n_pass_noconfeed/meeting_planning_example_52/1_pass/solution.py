import json
from z3 import *

def minutes_to_time_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Input parameters (as variables)
    # Locations
    RUSSIAN_HILL = "Russian Hill"
    RICHMOND = "Richmond District"

    # Travel times (in minutes)
    travel_rh_to_rich = 14
    travel_rich_to_rh = 13  # not used in this simple scenario, but included as input

    # Arrival at Russian Hill (start of the day)
    arrive_russian_hill = 9 * 60  # 9:00

    # Barbara's availability
    barbara_avail_start = 13 * 60 + 15  # 13:15
    barbara_avail_end = 18 * 60 + 15    # 18:15
    min_meet_duration = 45

    # Z3 variables
    dep_rh_to_rich = Int("dep_rh_to_rich")   # departure time from Russian Hill to Richmond
    arrive_rich = Int("arrive_rich")         # arrival time at Richmond
    meet_barbara = Bool("meet_barbara")      # whether we meet Barbara
    meet_start_b = Int("meet_start_b")       # meeting start time with Barbara
    meet_end_b = Int("meet_end_b")           # meeting end time with Barbara

    # Solver/Optimizer
    opt = Optimize()

    # Domain constraints for time variables (0..1440 minutes of the day)
    day_end = 24 * 60
    opt.add(dep_rh_to_rich >= arrive_russian_hill, dep_rh_to_rich <= day_end)
    opt.add(arrive_rich == dep_rh_to_rich + travel_rh_to_rich)
    opt.add(And(meet_start_b >= 0, meet_start_b <= day_end))
    opt.add(And(meet_end_b >= 0, meet_end_b <= day_end))

    # Meeting feasibility constraints (only bind if meeting happens)
    opt.add(Implies(meet_barbara, And(
        meet_start_b >= arrive_rich,                 # can't start before arriving
        meet_start_b >= barbara_avail_start,        # must be within Barbara's availability
        meet_end_b >= meet_start_b + min_meet_duration,  # minimum duration
        meet_end_b <= barbara_avail_end             # must end within availability
    )))

    # Objectives:
    # 1) Maximize number of friends met (only Barbara in this scenario)
    meet_count = If(meet_barbara, 1, 0)
    h1 = opt.maximize(meet_count)

    # 2) Maximize total meeting minutes
    total_meet_minutes = If(meet_barbara, meet_end_b - meet_start_b, 0)
    h2 = opt.maximize(total_meet_minutes)

    # 3) Minimize waiting time before meeting (arrive as just-in-time as possible)
    waiting_time = If(meet_barbara, meet_start_b - arrive_rich, 0)
    h3 = opt.minimize(waiting_time)

    # Solve
    result = opt.check()
    itinerary = []

    if result == sat:
        model = opt.model()

        if is_true(model.evaluate(meet_barbara, model_completion=True)):
            start_b = model.evaluate(meet_start_b, model_completion=True).as_long()
            end_b = model.evaluate(meet_end_b, model_completion=True).as_long()
            itinerary.append({
                "action": "meet",
                "location": RICHMOND,
                "person": "Barbara",
                "start_time": minutes_to_time_str(start_b),
                "end_time": minutes_to_time_str(end_b)
            })

    output = {
        "itinerary": itinerary
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()