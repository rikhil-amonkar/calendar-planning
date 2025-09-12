import z3
import json

solver = z3.Solver()

# Define variables
t_depart = z3.Int('t_depart')  # Departure time from Russian Hill (minutes since midnight)
meet_start = z3.Int('meet_start')  # Start time of meeting with Barbara (minutes since midnight)
duration = z3.Int('duration')  # Duration of meeting with Barbara (minutes)

# Constraints
solver.add(t_depart >= 540)  # Arrive at Russian Hill at 9:00 AM (540 min)
solver.add(meet_start >= 795)  # Barbara available from 1:15 PM (795 min)
solver.add(meet_start + duration <= 1095)  # Barbara leaves at 6:15 PM (1095 min)
solver.add(duration >= 45)  # Minimum meeting duration
solver.add(t_depart + 14 <= meet_start)  # Travel time from Russian Hill to Richmond

if solver.check() == z3.sat:
    model = solver.model()
    t_depart_val = model[t_depart].as_long()
    meet_start_val = model[meet_start].as_long()
    duration_val = model[duration].as_long()
    meet_end_val = meet_start_val + duration_val

    def to_time(m):
        h = m // 60
        mi = m % 60
        return f"{h}:{mi:02d}"

    itinerary = [
        {
            "action": "meet",
            "location": "Richmond District",
            "person": "Barbara",
            "start_time": to_time(meet_start_val),
            "end_time": to_time(meet_end_val)
        }
    ]
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))