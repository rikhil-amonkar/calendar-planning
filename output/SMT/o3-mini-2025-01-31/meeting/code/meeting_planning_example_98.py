from z3 import Optimize, Int, sat

# Create the optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from Alamo Square (in minutes after 9:00AM)
#   m_start : meeting start time at Richmond District (in minutes after 9:00AM)
#   m_end   : meeting end time at Richmond District (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Alamo Square to Richmond District is 12 minutes.
alamo_to_rd = 12

# Timothy's availability at Richmond District:
# 8:45PM is 11 hours and 45 minutes after 9:00AM -> 705 minutes.
# 9:30PM is 12 hours and 30 minutes after 9:00AM -> 750 minutes.
timothy_avail_from = 705
timothy_avail_until = 750

# CONSTRAINTS:

# 1. You arrive at Alamo Square at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart from Alamo Square at time d, you arrive at Richmond District at:
arrival_at_rd = d + alamo_to_rd

# 3. The meeting with Timothy cannot start before you arrive at Richmond District,
#    and cannot start before his availability begins.
opt.add(m_start >= arrival_at_rd)
opt.add(m_start >= timothy_avail_from)

# 4. The meeting must end by the time Timothy's availability ends.
opt.add(m_end <= timothy_avail_until)

# 5. You'd like to meet Timothy for at least 45 minutes.
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
    
    # Helper function: convert minutes after 9:00AM to HH:MM.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        # Adjust for day rollover if needed (though not expected here)
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Alamo Square at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Richmond District at: {to_time(d_val + alamo_to_rd)} (travel time = {alamo_to_rd} minutes)")
    print(f"  Meeting with Timothy starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Timothy ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")