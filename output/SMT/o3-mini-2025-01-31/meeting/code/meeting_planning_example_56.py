from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Chinatown (in minutes after 9:00AM)
#   m_start: meeting start time at Nob Hill (in minutes after 9:00AM)
#   m_end: meeting end time at Nob Hill (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Chinatown to Nob Hill is 8 minutes.
chinatown_to_nobhill = 8

# Joshua's availability at Nob Hill:
# From 10:15AM to 1:00PM.
# 10:15AM is 75 minutes after 9:00AM (since 9:00AM + 1 hour 15 minutes),
# and 1:00PM is 240 minutes after 9:00AM.
joshua_avail_from = 75
joshua_avail_until = 240

# Constraints:

# 1. You arrive at Chinatown at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. After departing, the arrival time at Nob Hill is:
arrival_at_nobhill = d + chinatown_to_nobhill

# 3. The meeting with Joshua cannot start until you have arrived at Nob Hill 
#    and not before Joshua's availability begins.
opt.add(m_start >= arrival_at_nobhill)
opt.add(m_start >= joshua_avail_from)

# 4. The meeting must end by the time Joshua's availability ends.
opt.add(m_end <= joshua_avail_until)

# 5. You'd like to meet Joshua for a minimum of 45 minutes.
opt.add(m_end - m_start >= 45)

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
    print(f"  Depart Chinatown at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Nob Hill at: {to_time(d_val + chinatown_to_nobhill)} (travel time = {chinatown_to_nobhill} minutes)")
    print(f"  Meeting with Joshua starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Joshua ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")