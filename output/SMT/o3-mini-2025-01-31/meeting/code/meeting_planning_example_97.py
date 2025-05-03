from z3 import Optimize, Int, sat

# Create the optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from Chinatown (in minutes after 9:00AM)
#   m_start : meeting start time at Richmond District (in minutes after 9:00AM)
#   m_end   : meeting end time at Richmond District (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Chinatown to Richmond District is 20 minutes.
chinatown_to_rd = 20

# Charles's availability at Richmond District:
# 6:00PM is 540 minutes after 9:00AM (9:00AM + 9 hours)
# 9:00PM is 720 minutes after 9:00AM (9:00AM + 12 hours)
charles_avail_from = 540
charles_avail_until = 720

# CONSTRAINTS:

# 1. You arrive at Chinatown at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart from Chinatown at time d,
#    you arrive at Richmond District at: d + chinatown_to_rd.
arrival_at_rd = d + chinatown_to_rd

# 3. The meeting with Charles cannot start before you arrive at Richmond District,
#    and cannot start before his availability begins.
opt.add(m_start >= arrival_at_rd)
opt.add(m_start >= charles_avail_from)

# 4. The meeting must end by the time Charles's availability ends.
opt.add(m_end <= charles_avail_until)

# 5. You’d like to meet Charles for at least 75 minutes.
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
    
    # Helper function: convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Chinatown at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Richmond District at: {to_time(d_val + chinatown_to_rd)} (travel time = {chinatown_to_rd} minutes)")
    print(f"  Meeting with Charles starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Charles ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")