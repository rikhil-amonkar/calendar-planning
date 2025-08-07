from z3 import *
import json

def solve_scheduling():
    s = Solver()

    # Define variables in minutes since 9:00 AM
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    william_start = Int('william_start')
    william_end = Int('william_end')

    # Convert time windows to minutes since 9:00 AM
    emily_min = 11*60 + 45 - 9*60  # 11:45 AM
    emily_max = 15*60 + 15 - 9*60  # 3:15 PM
    barbara_min = 16*60 + 45 - 9*60  # 4:45 PM
    barbara_max = 18*60 + 15 - 9*60  # 6:15 PM
    william_min = 17*60 + 15 - 9*60  # 5:15 PM
    william_max = 19*60 - 9*60  # 7:00 PM

    # Meeting duration constraints
    s.add(emily_end - emily_start >= 105)  # 1h45m with Emily
    s.add(barbara_end - barbara_start >= 60)  # 1h with Barbara
    s.add(william_end - william_start >= 105)  # 1h45m with William

    # Time window constraints
    s.add(emily_start >= emily_min)
    s.add(emily_end <= emily_max)
    s.add(barbara_start >= barbara_min)
    s.add(barbara_end <= barbara_max)
    s.add(william_start >= william_min)
    s.add(william_end <= william_max)

    # Travel times (minutes)
    castro_to_alamo = 8
    alamo_to_union = 14
    union_to_china = 7

    # Schedule order: Castro -> Alamo (Emily) -> Union (Barbara) -> Chinatown (William)
    s.add(emily_start >= castro_to_alamo)  # Travel to Emily
    s.add(barbara_start >= emily_end + alamo_to_union)  # Travel to Barbara
    s.add(william_start >= barbara_end + union_to_china)  # Travel to William

    if s.check() == sat:
        m = s.model()
        base = 9*60  # 9:00 AM in minutes

        def format_time(mins):
            h = (base + mins) // 60
            m = (base + mins) % 60
            return f"{h:02d}:{m:02d}"

        itinerary = [
            {"action": "meet", "person": "Emily", 
             "start_time": format_time(m[emily_start].as_long()),
             "end_time": format_time(m[emily_end].as_long())},
            {"action": "meet", "person": "Barbara",
             "start_time": format_time(m[barbara_start].as_long()),
             "end_time": format_time(m[barbara_end].as_long())},
            {"action": "meet", "person": "William",
             "start_time": format_time(m[william_start].as_long()),
             "end_time": format_time(m[william_end].as_long())}
        ]
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

print(json.dumps(solve_scheduling(), indent=2))