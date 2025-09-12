from z3 import *
import json

def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

# Input parameters
travel_time_russian_to_richmond = 14  # minutes
arrival_russian_hill_time = time_to_min("9:00")  # 9:00 AM
daniel_available_start = time_to_min("19:00")  # 7:00 PM
daniel_available_end = time_to_min("20:15")  # 8:15 PM
min_meeting_duration = 75  # minutes

# Z3 variables
departure_russian_hill = Int('departure_russian_hill')
meeting_start = Int('meeting_start')
meeting_end = Int('meeting_end')

s = Solver()

# Constraints
s.add(departure_russian_hill >= arrival_russian_hill_time)
s.add(departure_russian_hill + travel_time_russian_to_richmond <= meeting_start)
s.add(meeting_start >= daniel_available_start)
s.add(meeting_end <= daniel_available_end)
s.add(meeting_end - meeting_start >= min_meeting_duration)

if s.check() == sat:
    model = s.model()
    ms = model.evaluate(meeting_start).as_long()
    me = model.evaluate(meeting_end).as_long()

    itinerary = [
        {
            "action": "meet",
            "location": "Richmond District",
            "person": "Daniel",
            "start_time": min_to_time(ms),
            "end_time": min_to_time(me)
        }
    ]
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")