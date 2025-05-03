from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Nob Hill (in minutes after 9:00AM)
#   m_start: meeting start time at Presidio (in minutes after 9:00AM)
#   m_end: meeting end time at Presidio (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Nob Hill to Presidio is 17 minutes.
nobhill_to_presidio = 17

# Matthew's availability at Presidio:
# Available from 11:00AM to 3:15PM.
# 11:00AM is 11:00 - 9:00 = 2 hours after 9:00AM, i.e., 120 minutes.
# 3:15PM is 6 hours 15 minutes after 9:00AM, i.e., 375 minutes.
matthew_start = 120
matthew_end = 375

# Constraints:
# 1. You arrive at Nob Hill at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 17 minutes to travel from Nob Hill to Presidio.
arrival_at_presidio = d + nobhill_to_presidio

# 3. The meeting with Matthew cannot start until:
#    (a) You have arrived at Presidio.
#    (b) Matthew is available (from 11:00AM onward).
opt.add(m_start >= arrival_at_presidio)
opt.add(m_start >= matthew_start)

# 4. Matthew is available until 3:15PM.
opt.add(m_end <= matthew_end)

# 5. You'd like to meet Matthew for a minimum of 30 minutes.
opt.add(m_end - m_start >= 30)

# Objective: Maximize the meeting duration.
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
    print(f"  Depart Nob Hill at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Presidio at: {to_time(d_val + nobhill_to_presidio)} (travel time = {nobhill_to_presidio} minutes)")
    print(f"  Meeting with Matthew starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Matthew ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")