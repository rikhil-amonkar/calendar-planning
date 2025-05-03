from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# Time is measured in minutes after 9:00AM.
# Variables:
# d: departure time from Union Square (in minutes after 9:00AM)
# m_start: meeting start time at Nob Hill (in minutes after 9:00AM)
# m_end: meeting end time at Nob Hill (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Union Square to Nob Hill is 9 minutes.
union_to_nobhill = 9

# Mary's availability at Nob Hill:
# Mary is available from 12:00PM to 4:15PM.
# 12:00PM is 180 minutes after 9:00AM.
# 4:15PM is 435 minutes after 9:00AM.
mary_start = 180
mary_end = 435

# Constraints:
# 1. You arrive at Union Square at 9:00AM, and so you can only depart at or after 9:00AM.
opt.add(d >= 0)

# 2. After departing Union Square, you need 9 minutes to reach Nob Hill.
arrival_at_nobhill = d + union_to_nobhill

# 3. You cannot start the meeting until you have arrived at Nob Hill and Mary is there.
opt.add(m_start >= arrival_at_nobhill)
opt.add(m_start >= mary_start)

# 4. Mary is available only until 4:15PM.
opt.add(m_end <= mary_end)

# 5. You want to meet Mary for at least 75 minutes.
opt.add(m_end - m_start >= 75)

# Objective: Maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the optimization problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function to convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total = 9 * 60 + minutes_after_9
        hour = total // 60
        minute = total % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Union Square at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Nob Hill at: {to_time(d_val + union_to_nobhill)} (travel time = {union_to_nobhill} minutes)")
    print(f"  Meeting with Mary starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Mary ends at: {to_time(m_end_val)}")
    print(f"  Meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")