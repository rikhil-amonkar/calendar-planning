from z3 import Optimize, Int, sat

# Create the optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from Alamo Square (in minutes after 9:00AM)
#   m_start : meeting start time at Chinatown (in minutes after 9:00AM)
#   m_end   : meeting end time at Chinatown (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Alamo Square to Chinatown is 16 minutes.
alamo_to_chinatown = 16

# Laura's availability at Chinatown:
# She is available from 8:15AM to 6:45PM.
# Relative to 9:00AM, 8:15AM is -45 minutes and 6:45PM is 585 minutes (9:00AM + 9h45).
laura_avail_from = -45
laura_avail_until = 585

# CONSTRAINTS:

# 1. You arrive at Alamo Square at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart from Alamo Square at time d, you will arrive at Chinatown at:
arrival_at_chinatown = d + alamo_to_chinatown

# 3. The meeting with Laura cannot start before you arrive at Chinatown,
#    and cannot start before Laura's availability begins.
opt.add(m_start >= arrival_at_chinatown)
opt.add(m_start >= laura_avail_from)

# 4. The meeting must end by the time Laura's availability ends.
opt.add(m_end <= laura_avail_until)

# 5. You'd like to meet Laura for at least 15 minutes.
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
    
    # Helper function: convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Alamo Square at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Chinatown at: {to_time(d_val + alamo_to_chinatown)} (travel time = {alamo_to_chinatown} minutes)")
    print(f"  Meeting with Laura starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Laura ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")