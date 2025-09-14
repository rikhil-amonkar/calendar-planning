import json
from z3 import *

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def compute_schedule():
    # Input parameters as variables
    # Locations
    ALAMO_SQUARE = "Alamo Square"
    RICHMOND_DISTRICT = "Richmond District"

    # Travel times (minutes)
    travel_as_to_rd = 12
    travel_rd_to_as = 13  # Unused in this simple example but defined per input

    # Arrival time at Alamo Square
    arrive_as_time = 9 * 60  # 9:00

    # Timothy's availability at Richmond District
    timothy_name = "Timothy"
    timothy_location = RICHMOND_DISTRICT
    timothy_start = 20 * 60 + 45  # 20:45
    timothy_end = 21 * 60 + 30    # 21:30

    # Desired minimum meeting duration
    min_meet_duration = 45

    # SMT model
    opt = Optimize()

    # Decision variables
    depart_as_to_rd = Int('depart_as_to_rd')  # minute of day leaving Alamo Square
    arrive_rd = Int('arrive_rd')              # arrival time to Richmond District
    meet_tim = Bool('meet_tim')               # whether we meet Timothy
    meet_start_tim = Int('meet_start_tim')    # meeting start time with Timothy
    meet_end_tim = Int('meet_end_tim')        # meeting end time with Timothy
    meet_duration_tim = Int('meet_duration_tim')
    wait_before_meet_tim = Int('wait_before_meet_tim')

    # Base travel constraint
    opt.add(depart_as_to_rd >= arrive_as_time)
    opt.add(arrive_rd == depart_as_to_rd + travel_as_to_rd)

    # Meeting constraints conditional on actually meeting Timothy
    opt.add(Implies(meet_tim, And(
        meet_start_tim >= timothy_start,
        meet_start_tim >= arrive_rd,          # must have arrived before meeting starts
        meet_end_tim <= timothy_end,
        meet_end_tim > meet_start_tim,
        meet_end_tim - meet_start_tim >= min_meet_duration
    )))

    # Define duration and waiting
    opt.add(meet_duration_tim == If(meet_tim, meet_end_tim - meet_start_tim, 0))
    opt.add(wait_before_meet_tim == If(meet_tim, meet_start_tim - arrive_rd, 0))
    opt.add(wait_before_meet_tim >= 0)  # never negative

    # Objectives:
    # 1) Maximize number of friends met (only Timothy here)
    opt.maximize(If(meet_tim, 1, 0))
    # 2) Maximize meeting duration
    opt.maximize(meet_duration_tim)
    # 3) Minimize waiting time before the meeting
    opt.minimize(wait_before_meet_tim)

    # Solve
    if opt.check() != sat:
        # No feasible schedule
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    model = opt.model()

    itinerary = []

    if is_true(model.eval(meet_tim, model_completion=True)):
        start = model.eval(meet_start_tim, model_completion=True).as_long()
        end = model.eval(meet_end_tim, model_completion=True).as_long()
        itinerary.append({
            "action": "meet",
            "location": timothy_location,
            "person": timothy_name,
            "start_time": minutes_to_str(start),
            "end_time": minutes_to_str(end)
        })

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    compute_schedule()