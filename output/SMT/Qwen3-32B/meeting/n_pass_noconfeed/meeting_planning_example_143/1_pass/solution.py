import z3
import json

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

solver = z3.Solver()

# Define variables for Mark's meeting
start_mark = z3.Int('start_mark')
duration_mark = z3.Int('duration_mark')

# Mark's constraints: 1:00PM to 5:45PM (780 to 1065 minutes)
solver.add(start_mark >= 780)  # 1:00PM
solver.add(start_mark + duration_mark <= 1065)  # 5:45PM
solver.add(duration_mark >= 120)  # Minimum 120 minutes

# Karen's fixed meeting window: 6:45PM to 8:15PM (1125 to 1215 minutes)
# Travel from Embarcadero to Pacific Heights takes 11 minutes
# Need: end_mark + 11 <= 1125 => start_mark + duration_mark + 11 <= 1125
solver.add(start_mark + duration_mark + 11 <= 1125)

if solver.check() == z3.sat:
    model = solver.model()
    start_m = model[start_mark].as_long()
    dur_m = model[duration_mark].as_long()
    end_m = start_m + dur_m

    # Karen's meeting details
    start_k = 1125  # 6:45PM
    end_k = start_k + 90  # 8:15PM

    itinerary = [
        {
            "action": "meet",
            "location": "Embarcadero",
            "person": "Mark",
            "start_time": to_time_str(start_m),
            "end_time": to_time_str(end_m)
        },
        {
            "action": "meet",
            "location": "Pacific Heights",
            "person": "Karen",
            "start_time": to_time_str(start_k),
            "end_time": to_time_str(end_k)
        }
    ]

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))