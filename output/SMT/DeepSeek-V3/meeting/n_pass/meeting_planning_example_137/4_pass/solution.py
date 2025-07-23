from z3 import *
import json

def solve_scheduling():
    opt = Optimize()

    # Define variables
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')

    # Time in minutes since midnight
    start_time = 540  # 9:00 AM
    barbara_available_start = 495   # 8:15 AM
    barbara_available_end = 1140    # 7:00 PM
    kenneth_available_start = 720   # 12:00 PM
    kenneth_available_end = 900     # 3:00 PM

    # Travel times
    fd_to_chinatown = 5
    fd_to_golden_gate = 23
    chinatown_to_golden_gate = 23

    # Meeting durations
    min_barbara = 45
    min_kenneth = 90

    # Basic constraints
    opt.add(barbara_start >= barbara_available_start)
    opt.add(barbara_end <= barbara_available_end)
    opt.add(barbara_end - barbara_start >= min_barbara)
    
    opt.add(kenneth_start >= kenneth_available_start)
    opt.add(kenneth_end <= kenneth_available_end)
    opt.add(kenneth_end - kenneth_start >= min_kenneth)

    # Create two possible schedules
    schedule1 = Bool('schedule1')  # FD -> Chinatown -> Golden Gate Park
    schedule2 = Bool('schedule2')  # FD -> Golden Gate Park -> Chinatown
    
    # Only one schedule can be true
    opt.add(Or(schedule1, schedule2))
    opt.add(Not(And(schedule1, schedule2)))

    # Schedule 1: Meet Kenneth first
    opt.add(Implies(schedule1, kenneth_start >= start_time + fd_to_chinatown))
    opt.add(Implies(schedule1, barbara_start >= kenneth_end + chinatown_to_golden_gate))

    # Schedule 2: Meet Barbara first
    opt.add(Implies(schedule2, barbara_start >= start_time + fd_to_golden_gate))
    opt.add(Implies(schedule2, kenneth_start >= barbara_end + 23))  # Travel back to Chinatown

    # Ensure meetings don't overlap
    opt.add(Or(
        And(schedule1, barbara_start >= kenneth_end + chinatown_to_golden_gate),
        And(schedule2, kenneth_start >= barbara_end + 23)
    ))

    # Maximize total meeting time
    total_time = (barbara_end - barbara_start) + (kenneth_end - kenneth_start)
    opt.maximize(total_time)

    if opt.check() == sat:
        m = opt.model()
        barbara_start_val = m.evaluate(barbara_start).as_long()
        barbara_end_val = m.evaluate(barbara_end).as_long()
        kenneth_start_val = m.evaluate(kenneth_start).as_long()
        kenneth_end_val = m.evaluate(kenneth_end).as_long()

        def to_time(minutes):
            return f"{minutes//60:02d}:{minutes%60:02d}"

        itinerary = []
        if m.evaluate(schedule1):
            itinerary.append({
                "action": "meet",
                "person": "Kenneth",
                "start_time": to_time(kenneth_start_val),
                "end_time": to_time(kenneth_end_val)
            })
            itinerary.append({
                "action": "meet",
                "person": "Barbara",
                "start_time": to_time(barbara_start_val),
                "end_time": to_time(barbara_end_val)
            })
        else:
            itinerary.append({
                "action": "meet",
                "person": "Barbara",
                "start_time": to_time(barbara_start_val),
                "end_time": to_time(barbara_end_val)
            })
            itinerary.append({
                "action": "meet",
                "person": "Kenneth",
                "start_time": to_time(kenneth_start_val),
                "end_time": to_time(kenneth_end_val)
            })

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))