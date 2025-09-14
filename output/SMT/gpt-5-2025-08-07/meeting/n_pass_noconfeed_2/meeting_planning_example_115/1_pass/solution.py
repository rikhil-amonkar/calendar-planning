import json
from z3 import Optimize, Int, Bool, If, And, Or, Implies, Not, Sum

def minutes(h, m):
    return h * 60 + m

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Locations
    RD, PH, MD = 0, 1, 2
    location_names = {RD: "Richmond District", PH: "Pacific Heights", MD: "Marina District"}

    # Travel times (minutes), directional
    travel = {
        (RD, PH): 10,
        (RD, MD): 9,
        (PH, RD): 12,
        (PH, MD): 6,
        (MD, RD): 11,
        (MD, PH): 7,
    }

    # Start of the day
    day_start = minutes(9, 0)  # 9:00

    # Friends' constraints
    friends = {
        "Jessica": {
            "location": PH,
            "avail_start": minutes(15, 30),
            "avail_end": minutes(16, 45),
            "min_duration": 45
        },
        "Carol": {
            "location": MD,
            "avail_start": minutes(11, 30),
            "avail_end": minutes(15, 0),
            "min_duration": 60
        }
    }

    # Z3 variables
    start_J = Int("start_J")
    end_J = Int("end_J")
    meet_J = Bool("meet_J")

    start_C = Int("start_C")
    end_C = Int("end_C")
    meet_C = Bool("meet_C")

    j_before_c = Bool("j_before_c")  # if both met, determines the order

    opt = Optimize()
    opt.set(priority='lex')

    # Helper to constrain a meeting against availability and minimum duration
    def meeting_constraints(meet_var, start_var, end_var, avail_s, avail_e, min_dur):
        return Implies(
            meet_var,
            And(
                start_var >= avail_s,
                end_var <= avail_e,
                end_var - start_var >= min_dur
            )
        )

    # Apply basic constraints
    opt.add(meeting_constraints(meet_J, start_J, end_J,
                                friends["Jessica"]["avail_start"],
                                friends["Jessica"]["avail_end"],
                                friends["Jessica"]["min_duration"]))
    opt.add(meeting_constraints(meet_C, start_C, end_C,
                                friends["Carol"]["avail_start"],
                                friends["Carol"]["avail_end"],
                                friends["Carol"]["min_duration"]))

    # Non-negativity and ordering within each meeting (only when meeting)
    opt.add(Implies(meet_J, And(start_J >= 0, end_J >= 0, end_J >= start_J)))
    opt.add(Implies(meet_C, And(start_C >= 0, end_C >= 0, end_C >= start_C)))

    # Travel feasibility constraints
    # If both are met, enforce an order and respective travel times from day start and between meetings
    opt.add(Implies(And(meet_J, meet_C, j_before_c),
                    And(
                        start_J >= day_start + travel[(RD, friends["Jessica"]["location"])],
                        start_C >= end_J + travel[(friends["Jessica"]["location"], friends["Carol"]["location"])]
                    )))
    opt.add(Implies(And(meet_J, meet_C, Not(j_before_c)),
                    And(
                        start_C >= day_start + travel[(RD, friends["Carol"]["location"])],
                        start_J >= end_C + travel[(friends["Carol"]["location"], friends["Jessica"]["location"])]
                    )))

    # If only one meeting is met, ensure travel from start location (Richmond District) is accounted
    opt.add(Implies(And(meet_J, Not(meet_C)),
                    start_J >= day_start + travel[(RD, friends["Jessica"]["location"])]))
    opt.add(Implies(And(meet_C, Not(meet_J)),
                    start_C >= day_start + travel[(RD, friends["Carol"]["location"])]))

    # Objective: maximize the number of friends met
    meet_count = Sum(If(meet_J, 1, 0), If(meet_C, 1, 0))
    opt.maximize(meet_count)

    # Secondary objective: minimize the total end times (encourages earlier and shorter feasible meetings)
    total_end = If(meet_J, end_J, 0) + If(meet_C, end_C, 0)
    opt.minimize(total_end)

    if opt.check() != 1:  # sat
        print(json.dumps({"itinerary": []}))
        return

    model = opt.model()

    itinerary = []

    def add_meeting_if_scheduled(name, start_var, end_var):
        met = model.eval(meet_J if name == "Jessica" else meet_C, model_completion=True)
        if met is not None and met is True:
            start_val = model.eval(start_var, model_completion=True).as_long()
            end_val = model.eval(end_var, model_completion=True).as_long()
            itinerary.append({
                "action": "meet",
                "location": location_names[friends[name]["location"]],
                "person": name,
                "start_time": fmt_time(start_val),
                "end_time": fmt_time(end_val)
            })

    add_meeting_if_scheduled("Jessica", start_J, end_J)
    add_meeting_if_scheduled("Carol", start_C, end_C)

    # Sort by start time
    def parse_time_str(t):
        h, m = t.split(":")
        return int(h) * 60 + int(m)

    itinerary.sort(key=lambda x: parse_time_str(x["start_time"]))

    result = {"itinerary": itinerary}
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()