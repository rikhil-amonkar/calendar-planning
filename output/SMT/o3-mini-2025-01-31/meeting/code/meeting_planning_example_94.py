from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from Alamo Square (in minutes after 9:00AM)
#   m_start : meeting start time at Russian Hill (in minutes after 9:00AM)
#   m_end   : meeting end time at Russian Hill (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Alamo Square to Russian Hill is 13 minutes.
alamo_to_rh = 13

# James's availability at Russian Hill:
# 11:15AM is 135 minutes after 9:00AM (2 hours 15 minutes later).
# 12:00PM is 180 minutes after 9:00AM.
james_avail_from = 135
james_avail_until = 180

# CONSTRAINTS:

# 1. You arrive at Alamo Square at 9:00AM, so you cannot depart before then.
opt.add(d >= 0)

# 2. When you depart from Alamo Square at time d,
#    you arrive at Russian Hill at: d + alamo_to_rh.
arrival_at_rh = d + alamo_to_rh

# 3. The meeting with James cannot start before you arrive at Russian Hill,
#    and it cannot start before James's availability begins.
opt.add(m_start >= arrival_at_rh)
opt.add(m_start >= james_avail_from)

# 4. The meeting must end by the time James's availability ends.
opt.add(m_end <= james_avail_until)

# 5. You'd like to meet James for a minimum of 15 minutes.
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
    
    # Helper function: convert minutes after 9:00AM to HH:MM.
    def to_time(minutes_after_9):
        total_minutes = 9*60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Alamo Square at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Russian Hill at: {to_time(d_val + alamo_to_rh)} (Travel time = {alamo_to_rh} minutes)")
    print(f"  Meeting with James starts at: {to_time(m_start_val)}")
    print(f"  Meeting with James ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")