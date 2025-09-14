import json
from z3 import *

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Create an Optimize object
    opt = Optimize()

    # Define integer variables for start (s_) and end (e_) times (in minutes from midnight)
    s_D = Int('s_D')  # Daniel meeting start
    e_D = Int('e_D')  # Daniel meeting end
    s_M = Int('s_M')  # Margaret meeting start
    e_M = Int('e_M')  # Margaret meeting end
    s_C = Int('s_C')  # Charles meeting start
    e_C = Int('e_C')  # Charles meeting end
    s_S = Int('s_S')  # Stephanie meeting start
    e_S = Int('e_S')  # Stephanie meeting end

    # Boolean variable: if True, then morning order is Daniel then Margaret; if False, then Margaret then Daniel.
    morning_order = Bool('morning_order')

    # Travel times (in minutes) between locations.
    travel = {
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Mission District"): 24,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Mission District"): 10,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Mission District"): 16,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Mission District"): 17,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Golden Gate Park"): 17,
    }

    # List to hold all constraints.
    constraints = []

    # Friend availabilities (in minutes from midnight)
    # Daniel is at Golden Gate Park from 8:00 (480) to 13:30 (810) and requires at least 15 minutes.
    constraints.append(s_D >= 480)
    constraints.append(e_D <= 810)
    constraints.append(e_D - s_D >= 15)

    # Margaret is at Russian Hill from 9:00 (540) to 16:00 (960) and requires at least 30 minutes.
    constraints.append(s_M >= 540)
    constraints.append(e_M <= 960)
    constraints.append(e_M - s_M >= 30)

    # Charles is at Alamo Square from 18:00 (1080) to 20:45 (1245) and requires at least 90 minutes.
    constraints.append(s_C >= 1080)
    constraints.append(e_C <= 1245)
    constraints.append(e_C - s_C >= 90)

    # Stephanie is at Mission District from 20:30 (1230) to 22:00 (1320) and requires at least 90 minutes.
    constraints.append(s_S >= 1230)
    constraints.append(e_S <= 1320)
    constraints.append(e_S - s_S >= 90)

    # Initial condition: You arrive at Sunset District at 9:00 (540).
    # The first meeting in the morning must start after you travel from Sunset to that meeting location.
    # We impose different constraints based on the morning ordering.
    # If morning_order is True then Daniel is visited first.
    constraints.append(Implies(morning_order, s_D >= 540 + travel[("Sunset District", "Golden Gate Park")]))
    # And Margaret's meeting must start after Daniel's meeting plus travel from Golden Gate Park to Russian Hill.
    constraints.append(Implies(morning_order, s_M >= e_D + travel[("Golden Gate Park", "Russian Hill")]))
    
    # If morning_order is False then Margaret is visited first.
    constraints.append(Implies(Not(morning_order), s_M >= 540 + travel[("Sunset District", "Russian Hill")]))
    # And Daniel's meeting must begin after Margaret's meeting plus travel from Russian Hill to Golden Gate Park.
    constraints.append(Implies(Not(morning_order), s_D >= e_M + travel[("Russian Hill", "Golden Gate Park")]))
    
    # Evening meetings follow after the morning meetings.
    # If morning_order is True then the last morning meeting is Margaret; else it is Daniel.
    constraints.append(Implies(morning_order, s_C >= e_M + travel[("Russian Hill", "Alamo Square")]))
    constraints.append(Implies(Not(morning_order), s_C >= e_D + travel[("Golden Gate Park", "Alamo Square")]))
    
    # Transition from Charles's meeting to Stephanie's meeting.
    constraints.append(s_S >= e_C + travel[("Alamo Square", "Mission District")])
    
    # Add all constraints to the optimizer.
    for con in constraints:
        opt.add(con)

    # Objective: minimize the end time of the last meeting (Stephanie) to have an optimal early-finish schedule.
    opt.minimize(e_S)

    if opt.check() == sat:
        model = opt.model()
        # Decide morning order based on the model; True means Daniel then Margaret.
        morning_first = is_true(model.evaluate(morning_order))
        itinerary = []

        if morning_first:
            itinerary.append({
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Daniel",
                "start_time": format_time(model[s_D].as_long()),
                "end_time": format_time(model[e_D].as_long())
            })
            itinerary.append({
                "action": "meet",
                "location": "Russian Hill",
                "person": "Margaret",
                "start_time": format_time(model[s_M].as_long()),
                "end_time": format_time(model[e_M].as_long())
            })
        else:
            itinerary.append({
                "action": "meet",
                "location": "Russian Hill",
                "person": "Margaret",
                "start_time": format_time(model[s_M].as_long()),
                "end_time": format_time(model[e_M].as_long())
            })
            itinerary.append({
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Daniel",
                "start_time": format_time(model[s_D].as_long()),
                "end_time": format_time(model[e_D].as_long())
            })

        # Evening meetings (order fixed): Charles then Stephanie.
        itinerary.append({
            "action": "meet",
            "location": "Alamo Square",
            "person": "Charles",
            "start_time": format_time(model[s_C].as_long()),
            "end_time": format_time(model[e_C].as_long())
        })
        itinerary.append({
            "action": "meet",
            "location": "Mission District",
            "person": "Stephanie",
            "start_time": format_time(model[s_S].as_long()),
            "end_time": format_time(model[e_S].as_long())
        })

        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()