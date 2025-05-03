from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from Richmond District (in minutes after 9:00AM)
#   m_start : meeting start time at Alamo Square (in minutes after 9:00AM)
#   m_end   : meeting end time at Alamo Square (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Richmond District to Alamo Square is 13 minutes.
rd_to_alamo = 13

# Betty's availability at Alamo Square:
# 12:30PM is 210 minutes after 9:00AM.
# 7:15PM is 615 minutes after 9:00AM.
betty_avail_from = 210
betty_avail_until = 615

# CONSTRAINTS:

# 1. You are at Richmond District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart from Richmond District at time d, you arrive at Alamo Square after 13 minutes.
arrival_at_alamo = d + rd_to_alamo

# 3. The meeting with Betty cannot start before you have arrived at Alamo Square,
#    and cannot start before her availability begins.
opt.add(m_start >= arrival_at_alamo)
opt.add(m_start >= betty_avail_from)

# 4. The meeting must end by the time Betty's availability ends.
opt.add(m_end <= betty_avail_until)

# 5. You'd like to meet Betty for at least 75 minutes.
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
    
    # Helper function to convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Richmond District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Alamo Square at: {to_time(d_val + rd_to_alamo)} (travel time = {rd_to_alamo} minutes)")
    print(f"  Meeting with Betty starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Betty ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")