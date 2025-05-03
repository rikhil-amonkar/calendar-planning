from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from Sunset District (in minutes after 9:00AM)
#   m_start : meeting start time at Golden Gate Park (in minutes after 9:00AM)
#   m_end   : meeting end time at Golden Gate Park (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Sunset District to Golden Gate Park is 11 minutes.
sunset_to_ggp = 11

# Joshua's availability at Golden Gate Park:
# 8:45PM is 11 hours and 45 minutes after 9:00AM -> 705 minutes.
# 9:45PM is 12 hours and 45 minutes after 9:00AM -> 765 minutes.
joshua_avail_from = 705
joshua_avail_until = 765

# CONSTRAINTS:

# 1. You arrive at Sunset District at 9:00AM,
#    so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart from Sunset District at time d,
#    you arrive at Golden Gate Park at:
arrival_at_ggp = d + sunset_to_ggp

# 3. The meeting with Joshua cannot start before you arrive at Golden Gate Park,
#    and it cannot start before Joshua's availability begins.
opt.add(m_start >= arrival_at_ggp)
opt.add(m_start >= joshua_avail_from)

# 4. The meeting must end by Joshua's availability ending time.
opt.add(m_end <= joshua_avail_until)

# 5. You'd like to meet Joshua for at least 15 minutes.
opt.add(m_end - m_start >= 15)

# Objective: maximize the meeting duration (could potentially allow for a longer meeting within his availability).
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
    print(f"  Depart Sunset District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Golden Gate Park at: {to_time(d_val + sunset_to_ggp)} (travel time = {sunset_to_ggp} minutes)")
    print(f"  Meeting with Joshua starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Joshua ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")