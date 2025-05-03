from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Haight-Ashbury (in minutes after 9:00AM)
#   m_start: meeting start time at Russian Hill (in minutes after 9:00AM)
#   m_end: meeting end time at Russian Hill (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Haight-Ashbury to Russian Hill is 17 minutes.
ha_to_rh = 17

# Patricia's availability at Russian Hill:
# From 7:45AM to 2:15PM.
# Since we measure times relative to 9:00AM:
# 7:45AM is 1 hour 15 minutes before 9:00AM = -75 minutes.
# 2:15PM is 5 hours 15 minutes after 9:00AM = 315 minutes.
patricia_avail_from = -75
patricia_avail_until = 315

# Constraints:

# 1. You arrive at Haight-Ashbury at 9:00AM, therefore you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival time at Russian Hill is your departure time plus travel time.
arrival_at_rh = d + ha_to_rh

# 3. The meeting with Patricia can only start after you have arrived at Russian Hill and
#    not before her availability begins.
opt.add(m_start >= arrival_at_rh)
opt.add(m_start >= patricia_avail_from)

# 4. The meeting must end by the time Patricia's availability ends.
opt.add(m_end <= patricia_avail_until)

# 5. You'd like to meet Patricia for at least 30 minutes.
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
    
    # Helper function: convert minutes after 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Haight-Ashbury at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Russian Hill at: {to_time(d_val + ha_to_rh)} (travel time = {ha_to_rh} minutes)")
    print(f"  Meeting with Patricia starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Patricia ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")