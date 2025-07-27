from z3 import *
import json

def solve_scheduling():
    s = Solver()
    
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')
    
    start_time = 540  # 9:00 AM in minutes
    
    barbara_available_start = 495  # 8:15 AM
    barbara_available_end = 1140   # 7:00 PM
    kenneth_available_start = 720  # 12:00 PM
    kenneth_available_end = 900    # 3:00 PM
    
    fd_to_chinatown = 5
    fd_to_golden_gate = 23
    chinatown_to_golden_gate = 23
    golden_gate_to_chinatown = 23
    chinatown_to_fd = 5
    golden_gate_to_fd = 26
    
    s.add(barbara_start >= barbara_available_start)
    s.add(barbara_end <= barbara_available_end)
    s.add(barbara_end - barbara_start >= 45)
    
    s.add(kenneth_start >= kenneth_available_start)
    s.add(kenneth_end <= kenneth_available_end)
    s.add(kenneth_end - kenneth_start >= 90)
    
    meet_barbara_first = Bool('meet_barbara_first')
    
    s.add(Implies(meet_barbara_first, barbara_start >= start_time + fd_to_golden_gate))
    s.add(Implies(meet_barbara_first, kenneth_start >= barbara_end + golden_gate_to_chinatown))
    
    s.add(Implies(Not(meet_barbara_first), kenneth_start >= start_time + fd_to_chinatown))
    s.add(Implies(Not(meet_barbara_first), barbara_start >= kenneth_end + chinatown_to_golden_gate))
    
    total_meeting_time = (barbara_end - barbara_start) + (kenneth_end - kenneth_start)
    s.maximize(total_meeting_time)
    
    if s.check() == sat:
        m = s.model()
        barbara_start_val = m.evaluate(barbara_start).as_long()
        barbara_end_val = m.evaluate(barbara_end).as_long()
        kenneth_start_val = m.evaluate(kenneth_start).as_long()
        kenneth_end_val = m.evaluate(kenneth_end).as_long()
        
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        itinerary = [
            {"action": "meet", "person": "Barbara", "start_time": minutes_to_time(barbara_start_val), "end_time": minutes_to_time(barbara_end_val)},
            {"action": "meet", "person": "Kenneth", "start_time": minutes_to_time(kenneth_start_val), "end_time": minutes_to_time(kenneth_end_val)}
        ]
        
        itinerary.sort(key=lambda x: x["start_time"])
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))