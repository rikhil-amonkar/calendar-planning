from z3 import Optimize, Int, sat

# Create the optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from Marina District (in minutes after 9:00AM)
#   m_start : meeting start time at Nob Hill (in minutes after 9:00AM)
#   m_end   : meeting end time at Nob Hill (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Marina District to Nob Hill is 12 minutes.
marina_to_nh = 12

# Daniel's availability at Nob Hill:
# 7:45PM is 645 minutes after 9:00AM (10 hours 45 minutes),
# 9:00PM is 720 minutes after 9:00AM (12 hours).
daniel_avail_from = 645
daniel_avail_until = 720

# CONSTRAINTS:

# 1. You arrive at Marina District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart from Marina District, you arrive at Nob Hill at:
arrival_at_nh = d + marina_to_nh

# 3. The meeting with Daniel cannot start before you have arrived at Nob Hill 
#    and cannot start before his availability begins.
opt.add(m_start >= arrival_at_nh)
opt.add(m_start >= daniel_avail_from)

# 4. The meeting must end by the time Daniel's availability ends.
opt.add(m_end <= daniel_avail_until)

# 5. You'd like to meet Daniel for at least 15 minutes.
opt.add(m_end - m_start >= 15)

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
    print(f"  Depart Marina District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Nob Hill at: {to_time(d_val + marina_to_nh)} (travel time = {marina_to_nh} minutes)")
    print(f"  Meeting with Daniel starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Daniel ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")