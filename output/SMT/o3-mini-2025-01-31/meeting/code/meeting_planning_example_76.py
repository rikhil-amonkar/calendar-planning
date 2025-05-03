from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d      : departure time from Marina District (in minutes after 9:00AM)
#   m_start: meeting start time at Haight-Ashbury (in minutes after 9:00AM)
#   m_end  : meeting end time at Haight-Ashbury (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Marina District to Haight-Ashbury is 16 minutes.
marina_to_ha = 16

# Timothy's availability at Haight-Ashbury:
# From 5:00PM to 8:15PM.
# 5:00PM is 480 minutes after 9:00AM.
# 8:15PM is 675 minutes after 9:00AM.
timothy_avail_from = 480
timothy_avail_until = 675

# CONSTRAINTS:

# 1. You arrive at Marina District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival time at Haight-Ashbury is your departure time plus travel time.
arrival_at_ha = d + marina_to_ha

# 3. The meeting with Timothy can only start after you have arrived at Haight-Ashbury,
#    and not before his availability begins.
opt.add(m_start >= arrival_at_ha)
opt.add(m_start >= timothy_avail_from)

# 4. The meeting must end by the time Timothy's availability ends.
opt.add(m_end <= timothy_avail_until)

# 5. You'd like to meet Timothy for at least 60 minutes.
opt.add(m_end - m_start >= 60)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function: converts minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Marina District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Haight-Ashbury at: {to_time(d_val + marina_to_ha)} (travel time = {marina_to_ha} minutes)")
    print(f"  Meeting with Timothy starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Timothy ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")