from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Bayview (in minutes after 9:00AM)
#   m_start: meeting start time at Russian Hill (in minutes after 9:00AM)
#   m_end: meeting end time at Russian Hill (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Bayview to Russian Hill is 23 minutes.
bayview_to_russianhill = 23

# John's availability at Russian Hill:
# 5:30PM is 8.5 hours after 9:00AM -> 8.5 * 60 = 510 minutes.
# 9:00PM is 12 hours after 9:00AM -> 12 * 60 = 720 minutes.
john_available_from = 510
john_available_until = 720

# Constraints:
# 1. You arrive at Bayview at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 23 minutes to travel from Bayview to Russian Hill.
arrival_at_russianhill = d + bayview_to_russianhill

# 3. The meeting with John cannot start until you have arrived at Russian Hill
#    and until John is available.
opt.add(m_start >= arrival_at_russianhill)
opt.add(m_start >= john_available_from)

# 4. John is available only until 9:00PM.
opt.add(m_end <= john_available_until)

# 5. You'd like to meet John for a minimum of 75 minutes.
opt.add(m_end - m_start >= 75)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function to convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Bayview at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Russian Hill at: {to_time(d_val + bayview_to_russianhill)} (travel time = {bayview_to_russianhill} minutes)")
    print(f"  Meeting with John starts at: {to_time(m_start_val)}")
    print(f"  Meeting with John ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")