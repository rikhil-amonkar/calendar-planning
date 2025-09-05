import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Not, is_true, sat

def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
        # Input parameters (can be adjusted as needed)
        # Locations
        RUSSIAN_HILL = "Russian Hill"
        RICHMOND_DISTRICT = "Richmond District"

        # Travel times in minutes
        travel_RH_to_RD = 14
        travel_RD_to_RH = 13  # Provided but not required for this single meeting

        # Arrival to city
        arrive_RH_time = 9 * 60  # 9:00

        # Daniel's availability at Richmond District
        daniel_location = RICHMOND_DISTRICT
        daniel_avail_start = 19 * 60       # 19:00
        daniel_avail_end = 20 * 60 + 15    # 20:15

        # Desired minimum meeting duration
        min_meet_duration = 75

        # SMT variables
        opt = Optimize()

        meet_daniel = Bool("meet_daniel")

        depart_time_from_RH = Int("depart_time_from_RH")  # time we depart from Russian Hill
        arrive_time_RD = Int("arrive_time_RD")            # arrival time at Richmond District

        meet_start = Int("meet_start")  # meeting start time with Daniel at Richmond
        meet_end = Int("meet_end")      # meeting end time with Daniel at Richmond

        # General bounds
        day_min = 0
        day_max = 24 * 60 + 59  # allow up to 23:59

        opt.add(depart_time_from_RH >= arrive_RH_time)
        opt.add(depart_time_from_RH <= day_max)
        opt.add(arrive_time_RD == depart_time_from_RH + travel_RH_to_RD)
        opt.add(arrive_time_RD >= day_min)
        opt.add(arrive_time_RD <= day_max)

        opt.add(meet_start >= day_min, meet_start <= day_max)
        opt.add(meet_end >= day_min, meet_end <= day_max)

        # If we meet Daniel, the meeting must be within his availability at the set location
        # and respect travel times from Russian Hill.
        opt.add(Implies(
            meet_daniel,
            And(
                meet_start >= daniel_avail_start,
                meet_end <= daniel_avail_end,
                meet_end > meet_start,
                meet_end - meet_start >= min_meet_duration,
                # Must arrive to Richmond District before meeting starts
                arrive_time_RD <= meet_start
            )
        ))

        # If we do not meet Daniel, neutralize meeting variables to avoid spurious solutions
        opt.add(Implies(Not(meet_daniel), meet_end == meet_start))

        # Objectives:
        # 1) Maximize whether we meet Daniel (1 if yes, 0 if no)
        # 2) Maximize meeting duration (secondary), in case there were multiple choices
        meet_flag = If(meet_daniel, 1, 0)
        duration_if_meet = If(meet_daniel, meet_end - meet_start, 0)

        opt.maximize(meet_flag)
        opt.maximize(duration_if_meet)

        # Solve
        if opt.check() != sat:
            # No feasible schedule
            output = {"itinerary": []}
            print(json.dumps(output))
            return

        model = opt.model()

        itinerary = []

        if is_true(model.eval(meet_daniel, model_completion=True)):
            s = model.eval(meet_start, model_completion=True).as_long()
            e = model.eval(meet_end, model_completion=True).as_long()
            itinerary.append({
                "action": "meet",
                "location": daniel_location,
                "person": "Daniel",
                "start_time": minutes_to_str(s),
                "end_time": minutes_to_str(e)
            })

        output = {"itinerary": itinerary}
        print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()