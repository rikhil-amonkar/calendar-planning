from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are expressed in minutes after 9:00AM.
# Variables:
#   d: departure time from Marina District (in minutes after 9:00AM)
#   m_start: meeting start time at Pacific Heights (in minutes after 9:00AM)
#   m_end: meeting end time at Pacific Heights (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Marina District to Pacific Heights is 7 minutes.
marina_to_pacific = 7

# Margaret's availability at Pacific Heights:
# 7:00PM is 10 hours after 9:00AM -> 600 minutes.
# 7:45PM is 10 hours 45 minutes after 9:00AM -> 645 minutes.
margaret_available_from = 600
margaret_available_until = 645

# Constraints:

# 1. You arrive at Marina District at 9:00AM and cannot depart before then.
opt.add(d >= 0)

# 2. It takes 7 minutes to travel from Marina District to Pacific Heights.
arrival_at_pacific = d + marina_to_pacific

# 3. The meeting with Margaret cannot start until you have arrived at Pacific Heights
#    and until Margaret is available.
opt.add(m_start >= arrival_at_pacific)
opt.add(m_start >= margaret_available_from)

# 4. Margaret is available until 7:45PM.
opt.add(m_end <= margaret_available_until)

# 5. You'd like to meet Margaret for at least 15 minutes.
opt.add(m_end - m_start >= 15)

# Objective: maximize the meeting duration
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function to convert minutes after 9:00AM to a HH:MM string.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Marina District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Pacific Heights at: {to_time(d_val + marina_to_pacific)} (travel time = {marina_to_pacific} minutes)")
    print(f"  Meeting with Margaret starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Margaret ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")