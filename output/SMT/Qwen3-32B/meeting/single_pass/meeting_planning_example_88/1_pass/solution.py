import z3
import json

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

solver = z3.Solver()

t_depart = z3.Int('t_depart')
t_start = z3.Int('t_start')
t_end = z3.Int('t_end')

# 9:00 AM is 9*60 = 540 minutes
solver.add(t_depart >= 540)
# arrival time is t_depart + 11, so t_start >= arrival time
solver.add(t_start >= t_depart + 11)
# Joshua's available from 8:45 PM (20:45) which is 20*60 +45 = 1245
solver.add(t_start >= 1245)
# meeting must be at least 15 minutes
solver.add(t_end >= t_start + 15)
# Joshua is available until 9:45 PM (21:45) which is 21*60+45=1305
solver.add(t_end <= 1305)

if solver.check() == z3.sat:
    model = solver.model()
    start = model[t_start].as_long()
    end = model[t_end].as_long()
    itinerary = [{
        "action": "meet",
        "person": "Joshua",
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    }]
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found")