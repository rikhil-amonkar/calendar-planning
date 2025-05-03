from z3 import Optimize, Int, sat

# Create the optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Marina District
#   m_start: meeting start time at Richmond District
#   m_end: meeting end time at Richmond District
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Marina District to Richmond District is 11 minutes.
marina_to_richmond = 11

# Betty's availability at Richmond District:
# 8:30PM is 11 hours 30 minutes after 9:00AM -> 11*60 + 30 = 690 minutes.
# 10:00PM is 13 hours after 9:00AM -> 13*60 = 780 minutes.
betty_start = 690
betty_end = 780

# Constraints:
# 1. You arrive at Marina District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. After departing from Marina District, the travel time to Richmond District is 11 minutes.
arrival_at_richmond = d + marina_to_richmond

# 3. The meeting with Betty cannot start until:
#    - You have arrived at Richmond District.
#    - Betty is available at Richmond District.
opt.add(m_start >= arrival_at_richmond)
opt.add(m_start >= betty_start)

# 4. Betty is available until 10:00PM.
opt.add(m_end <= betty_end)

# 5. You would like to meet Betty for at least 75 minutes.
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
    
    # Helper function to convert minutes after 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Marina District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Richmond District at: {to_time(d_val + marina_to_richmond)} (travel time = {marina_to_richmond} minutes)")
    print(f"  Meeting with Betty starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Betty ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")