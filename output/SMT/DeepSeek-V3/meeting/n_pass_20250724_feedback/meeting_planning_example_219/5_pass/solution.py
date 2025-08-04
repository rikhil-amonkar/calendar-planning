from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for meeting start and end times (in minutes since midnight)
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    william_start = Int('william_start')
    william_end = Int('william_end')

    # Travel times in minutes
    travel = {
        'castro_to_alamo': 8,
        'alamo_to_union': 14,
        'union_to_china': 7
    }

    # Time windows in minutes since midnight
    windows = {
        'emily': (11*60 + 45, 15*60 + 15),  # 11:45 AM - 3:15 PM
        'barbara': (16*60 + 45, 18*60 + 15),  # 4:45 PM - 6:15 PM
        'william': (17*60 + 15, 19*60 + 0)    # 5:15 PM - 7:00 PM
    }

    # Starting time at The Castro (9:00 AM)
    start_time = 9 * 60

    # Meeting duration constraints
    s.add(emily_end - emily_start >= 105)  # Emily: 105 minutes
    s.add(barbara_end - barbara_start >= 60)  # Barbara: 60 minutes
    s.add(william_end - william_start >= 105)  # William: 105 minutes

    # Time window constraints
    s.add(emily_start >= windows['emily'][0], emily_end <= windows['emily'][1])
    s.add(barbara_start >= windows['barbara'][0], barbara_end <= windows['barbara'][1])
    s.add(william_start >= windows['william'][0], william_end <= windows['william'][1])

    # Travel constraints
    s.add(emily_start >= start_time + travel['castro_to_alamo'])
    s.add(barbara_start >= emily_end + travel['alamo_to_union'])
    s.add(william_start >= barbara_end + travel['union_to_china'])

    # Additional constraint: Barbara must finish before William's meeting starts
    s.add(barbara_end <= william_start)

    # Check for solution
    if s.check() == sat:
        model = s.model()
        def minutes_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        itinerary = [
            {"action": "meet", "person": "Emily", 
             "start_time": minutes_to_time(model[emily_start].as_long()),
             "end_time": minutes_to_time(model[emily_end].as_long())},
            {"action": "meet", "person": "Barbara",
             "start_time": minutes_to_time(model[barbara_start].as_long()),
             "end_time": minutes_to_time(model[barbara_end].as_long())},
            {"action": "meet", "person": "William",
             "start_time": minutes_to_time(model[william_start].as_long()),
             "end_time": minutes_to_time(model[william_end].as_long())}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found."}

result = solve_scheduling()
print(json.dumps(result, indent=2))