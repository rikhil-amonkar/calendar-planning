from z3 import *

def min_to_time(mins_after_9am):
    total_mins = mins_after_9am
    hours = total_mins // 60
    minutes = total_mins % 60
    abs_hour = 9 + hours
    period = "AM" if abs_hour < 12 else "PM"
    hour12 = (abs_hour - 1) % 12 + 1
    return f"{hour12}:{minutes:02d}{period}"

# Create the variables
depart_NH = Int('depart_NH')
depart_P = Int('depart_P')

# Create the optimizer
opt = Optimize()

# Arrival time at Presidio
arrive_P = depart_NH + 17

# Constraints
opt.add(depart_NH >= 0)
opt.add(depart_P >= arrive_P)

# Meeting duration constraints
start_meeting = If(arrive_P < 135, 135, arrive_P)
end_meeting = If(depart_P > 525, 525, depart_P)
meeting_duration = end_meeting - start_meeting
opt.add(meeting_duration >= 120)

# Objective: maximize depart_NH to leave as late as possible
opt.maximize(depart_NH)

if opt.check() == sat:
    m = opt.model()
    depart_NH_val = m.eval(depart_NH).as_long()
    depart_P_val = m.eval(depart_P).as_long()
    arrive_P_val = depart_NH_val + 17

    print("Leave Nob Hill at:", min_to_time(depart_NH_val))
    print("Arrive at Presidio at:", min_to_time(arrive_P_val))
    print("Leave Presidio at:", min_to_time(depart_P_val))
else:
    print("No solution found")