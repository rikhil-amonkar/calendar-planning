from z3 import *
import json

# Convert minutes since midnight to HH:MM format
def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define variables
start_laura, end_laura = Ints('start_laura end_laura')
start_thomas, end_thomas = Ints('start_thomas end_thomas')
start_patricia, end_patricia = Ints('start_patricia end_patricia')
start_stephanie, end_stephanie = Ints('start_stephanie end_stephanie')
start_betty, end_betty = Ints('start_betty end_betty')

solver = Solver()

# Laura constraints
solver.add(start_laura >= 551)  # arrival at Nob Hill after travel from FW
solver.add(end_laura == start_laura + 30)
solver.add(end_laura <= 975)  # 4:15 PM

# Thomas constraints
solver.add(start_thomas >= 930)  # 3:30 PM
solver.add(end_thomas == start_thomas + 120)
solver.add(end_thomas <= 1110)  # 6:30 PM

# Patricia constraints
solver.add(start_patricia >= 1050)  # 5:30 PM
solver.add(end_patricia == start_patricia + 45)
solver.add(end_patricia <= 1320)  # 10:00 PM

# Stephanie constraints
solver.add(start_stephanie >= 1110)  # 6:30 PM
solver.add(end_stephanie == start_stephanie + 30)
solver.add(end_stephanie <= 1305)  # 9:45 PM

# Betty constraints
solver.add(start_betty >= 1125)  # 6:45 PM
solver.add(end_betty == start_betty + 45)
solver.add(end_betty <= 1305)  # 9:45 PM

# Travel constraints
solver.add(start_thomas >= start_laura + 30 + 19)  # end_laura + 19
solver.add(start_patricia >= start_thomas + 120 + 19)  # end_thomas +19
solver.add(start_stephanie >= start_patricia + 45 + 25)  # end_patricia +25
solver.add(start_betty >= start_stephanie + 30 + 16)  # end_stephanie +16

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Extract values
    sl = model[start_laura].as_long()
    el = model[end_laura].as_long()
    st = model[start_thomas].as_long()
    et = model[end_thomas].as_long()
    sp = model[start_patricia].as_long()
    ep = model[end_patricia].as_long()
    sss = model[start_stephanie].as_long()
    ess = model[end_stephanie].as_long()
    sb = model[start_betty].as_long()
    eb = model[end_betty].as_long()
    
    # Create the itinerary
    itinerary = [
        {"action": "meet", "person": "Laura", "start_time": to_time_str(sl), "end_time": to_time_str(el)},
        {"action": "meet", "person": "Thomas", "start_time": to_time_str(st), "end_time": to_time_str(et)},
        {"action": "meet", "person": "Patricia", "start_time": to_time_str(sp), "end_time": to_time_str(ep)},
        {"action": "meet", "person": "Stephanie", "start_time": to_time_str(sss), "end_time": to_time_str(ess)},
        {"action": "meet", "person": "Betty", "start_time": to_time_str(sb), "end_time": to_time_str(eb)},
    ]
    # Output as JSON
    solution = {"itinerary": itinerary}
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")