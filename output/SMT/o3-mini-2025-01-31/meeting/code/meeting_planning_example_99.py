from z3 import Optimize, Int, sat

# Create the optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from Fisherman's Wharf (in minutes after 9:00AM)
#   m_start : meeting start time at Union Square (in minutes after 9:00AM)
#   m_end   : meeting end time at Union Square (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Fisherman's Wharf to Union Square is 13 minutes.
fw_to_us = 13

# Kevin's availability at Union Square:
# 1:15PM is 4 hours and 15 minutes after 9:00AM -> 4*60 + 15 = 255 minutes.
# 7:15PM is 10 hours and 15 minutes after 9:00AM -> 10*60 + 15 = 615 minutes.
kevin_avail_from = 255
kevin_avail_until = 615

# CONSTRAINTS:

# 1. You arrive at Fisherman's Wharf at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart from Fisherman's Wharf at time d, you arrive at Union Square at time (d + fw_to_us).
arrival_at_us = d + fw_to_us

# 3. The meeting with Kevin cannot start before you arrive at Union Square,
#    and it cannot start before Kevin's availability begins.
opt.add(m_start >= arrival_at_us)
opt.add(m_start >= kevin_avail_from)

# 4. The meeting must end by the time Kevin's availability ends.
opt.add(m_end <= kevin_avail_until)

# 5. You'd like to meet Kevin for at least 15 minutes.
opt.add(m_end - m_start >= 15)

# Objective: Maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()

    # Helper function: convert minutes after 9:00AM to HH:MM format
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    print("Optimal Schedule:")
    print(f"  Depart Fisherman's Wharf at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Union Square at: {to_time(d_val + fw_to_us)} (travel time = {fw_to_us} minutes)")
    print(f"  Meeting with Kevin starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Kevin ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")