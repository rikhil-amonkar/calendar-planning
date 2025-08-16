import z3
import json

def minutes_since_midnight(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def time_to_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Convert arrival time at Nob Hill to minutes
arrival_nob_hill = minutes_since_midnight("09:00")  # 540

# Robert's available time
robert_start = minutes_since_midnight("11:15")  # 675
robert_end = minutes_since_midnight("17:45")    # 1065

# Travel time from Nob Hill to Presidio
travel_time = 17

# Variables for the meeting with Robert
start = z3.Int('start')
end = z3.Int('end')

solver = z3.Solver()

# Constraints for Robert's meeting
solver.add(start >= robert_start)
solver.add(end >= start + 120)
solver.add(end <= robert_end)

# Constraint for travel time
solver.add(start - travel_time >= arrival_nob_hill)

if solver.check() == z3.sat:
    model = solver.model()
    start_val = model[start].as_long()
    end_val = model[end].as_long()
    # Convert to time strings
    start_time_str = time_to_str(start_val)
    end_time_str = time_to_str(end_val)
    itinerary = [{"action": "meet", "person": "Robert", "start_time": start_time_str, "end_time": end_time_str}]
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found")