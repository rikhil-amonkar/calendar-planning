from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Bayview (in minutes after 9:00AM)
#   m_start: meeting start time at Pacific Heights (in minutes after 9:00AM)
#   m_end: meeting end time at Pacific Heights (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Bayview to Pacific Heights is 23 minutes.
bayview_to_pacific = 23

# Thomas's availability at Pacific Heights:
# Thomas is available from 12:15PM to 5:15PM.
# 12:15PM is 3 hours 15 minutes after 9:00AM (195 minutes after 9:00AM).
# 5:15PM is 8 hours 15 minutes after 9:00AM (495 minutes after 9:00AM).
thomas_available_from = 195
thomas_available_until = 495

# Constraints:

# 1. You arrive at Bayview at 9:00AM so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 23 minutes to travel from Bayview to Pacific Heights.
arrival_at_pacific = d + bayview_to_pacific

# 3. The meeting with Thomas cannot start until you have arrived at Pacific Heights
#    and until Thomas is available.
opt.add(m_start >= arrival_at_pacific)
opt.add(m_start >= thomas_available_from)

# 4. Thomas is available until 5:15PM.
opt.add(m_end <= thomas_available_until)

# 5. You'd like to meet Thomas for a minimum of 105 minutes.
opt.add(m_end - m_start >= 105)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function to convert minutes after 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Bayview at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Pacific Heights at: {to_time(d_val + bayview_to_pacific)} (travel time = {bayview_to_pacific} minutes)")
    print(f"  Meeting with Thomas starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Thomas ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")