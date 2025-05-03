from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d      : departure time from Richmond District (in minutes after 9:00AM)
#   m_start: meeting start time at Golden Gate Park (in minutes after 9:00AM)
#   m_end  : meeting end time at Golden Gate Park (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Richmond District to Golden Gate Park is 9 minutes.
rd_to_ggp = 9

# Robert's availability at Golden Gate Park:
# Starts at 8:15AM which is 45 minutes before 9:00AM -> -45 minutes.
# Ends at 8:30PM which is 11.5 hours after 9:00AM -> 690 minutes.
robert_avail_from = -45
robert_avail_until = 690

# CONSTRAINTS:

# 1. You arrive at Richmond District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival time at Golden Gate Park is your departure time plus travel time.
arrival_at_ggp = d + rd_to_ggp

# 3. The meeting with Robert can't start before you arrive and not before his availability begins.
opt.add(m_start >= arrival_at_ggp)
opt.add(m_start >= robert_avail_from)

# 4. The meeting must end by the time Robert's availability ends.
opt.add(m_end <= robert_avail_until)

# 5. You'd like to meet Robert for at least 30 minutes.
opt.add(m_end - m_start >= 30)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function: Convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Richmond District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Golden Gate Park at: {to_time(d_val + rd_to_ggp)} (travel time = {rd_to_ggp} minutes)")
    print(f"  Meeting with Robert starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Robert ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")