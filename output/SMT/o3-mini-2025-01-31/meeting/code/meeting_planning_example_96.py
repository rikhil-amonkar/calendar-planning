from z3 import Optimize, Int, sat

# Create the optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : the departure time from Sunset District (in minutes after 9:00AM)
#   m_start : the meeting start time at Nob Hill (in minutes after 9:00AM)
#   m_end   : the meeting end time at Nob Hill (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Sunset District to Nob Hill is 27 minutes.
sunset_to_nobhill = 27

# Rebecca's availability at Nob Hill:
# She is available from 9:00AM to 6:15PM.
# 9:00AM is 0 minutes after 9:00AM.
# 6:15PM is 9 hours and 15 minutes after 9:00AM, i.e., (9 * 60) + 15 = 555 minutes.
rebecca_avail_from = 0
rebecca_avail_until = 555

# CONSTRAINTS:

# 1. You arrive at Sunset District at 9:00AM, so you cannot depart before that time.
opt.add(d >= 0)

# 2. When you depart from Sunset District at time d,
#    you will arrive at Nob Hill at time (d + sunset_to_nobhill).
arrival_at_nobhill = d + sunset_to_nobhill

# 3. The meeting with Rebecca cannot start before you arrive at Nob Hill 
#    and cannot start before Rebecca's availability begins.
opt.add(m_start >= arrival_at_nobhill)
opt.add(m_start >= rebecca_avail_from)

# 4. The meeting must end by the time Rebecca's availability ends.
opt.add(m_end <= rebecca_avail_until)

# 5. You'd like to meet Rebecca for at least 30 minutes.
opt.add(m_end - m_start >= 30)

# Objective: maximize the meeting duration (m_end - m_start).
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val      = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val   = model[m_end].as_long()
    
    # Helper function: convert minutes after 9:00AM to a HH:MM formatted string.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Sunset District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Nob Hill at: {to_time(d_val + sunset_to_nobhill)} (travel time = {sunset_to_nobhill} minutes)")
    print(f"  Meeting with Rebecca starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Rebecca ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")