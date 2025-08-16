import z3
import json

solver = z3.Solver()

start_steph = z3.Int('start_steph')
start_john = z3.Int('start_john')

# Stephanie's arrival at Financial District (9:05 AM = 545 minutes)
solver.add(start_steph >= 545)
# Stephanie's meeting must end by 11:30 AM (690 minutes)
solver.add(start_steph <= 600)  # 10:00 AM

# John's meeting constraints
# Travel from Financial District to Alamo Square (17 minutes)
solver.add(start_john >= start_steph + 90 + 17)
# John is available from 10:15 AM (615 minutes)
solver.add(start_john >= 615)
# John's meeting must end by 8:45 PM (1245 minutes)
solver.add(start_john + 30 <= 1245)

if solver.check() == z3.sat:
    model = solver.model()
    ss_val = model[start_steph].as_long()
    sj_val = model[start_john].as_long()

    def to_time_str(m):
        h = m // 60
        return f"{h:02d}:{m % 60:02d}"

    itinerary = [
        {
            "action": "meet", 
            "person": "Stephanie", 
            "start_time": to_time_str(ss_val), 
            "end_time": to_time_str(ss_val + 90)
        },
        {
            "action": "meet", 
            "person": "John", 
            "start_time": to_time_str(sj_val), 
            "end_time": to_time_str(sj_val + 30)
        }
    ]
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))