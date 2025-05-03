from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# Define time variables (all in minutes after 9:00AM):
# d: departure time from Chinatown
# m_start: meeting start time at Russian Hill
# m_end: meeting end time at Russian Hill
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time (in minutes):
chinatown_to_russianhill = 7

# Ronald's availability at Russian Hill:
# 3:15PM is 6 hours 15 minutes after 9:00AM = 375 minutes.
# 9:30PM is 12 hours 30 minutes after 9:00AM = 750 minutes.
ronald_arrival = 375
ronald_departure = 750

# Constraint 1: You arrive at Chinatown at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# Constraint 2: Traveling from Chinatown to Russian Hill takes 7 minutes.
arrival_at_russianhill = d + chinatown_to_russianhill

# Constraint 3: The meeting with Ronald can only begin after you have arrived at Russian Hill 
# and after Ronald has arrived.
opt.add(m_start >= arrival_at_russianhill)
opt.add(m_start >= ronald_arrival)

# Constraint 4: Ronald is available until 9:30PM.
opt.add(m_end <= ronald_departure)

# Constraint 5: You'd like to meet Ronald for at least 105 minutes.
opt.add(m_end - m_start >= 105)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduler.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()

    # A helper function to convert minutes after 9:00AM to HH:MM string.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    print("Optimal Schedule:")
    print(f"  Depart Chinatown at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Russian Hill at: {to_time(d_val + chinatown_to_russianhill)} (travel time = {chinatown_to_russianhill} minutes)")
    print(f"  Meeting with Ronald starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Ronald ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")