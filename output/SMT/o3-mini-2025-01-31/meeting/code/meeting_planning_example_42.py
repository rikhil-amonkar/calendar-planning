from z3 import Optimize, Int, sat

# Create an optimizer instance.
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

# Timothy's availability at Presidio:
# From 1:00PM to 7:00PM.
# 1:00PM is 4 hours after 9:00AM: 240 minutes after 9:00AM.
# 7:00PM is 10 hours after 9:00AM: 600 minutes after 9:00AM.
timothy_avail_from = 240
timothy_avail_until = 600

# Constraints:

# 1. You arrive at Nob Hill at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 17 minutes to travel from Nob Hill to Presidio.
arrival_at_presidio = d + nobhill_to_presidio

# 3. The meeting with Timothy cannot start until you have arrived at Presidio
#    and not before Timothy's availability begins.
opt.add(m_start >= arrival_at_presidio)
opt.add(m_start >= timothy_avail_from)

# 4. The meeting must end by the time Timothy is available until.
opt.add(m_end <= timothy_avail_until)

# 5. You'd like to meet Timothy for a minimum of 30 minutes.
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
    
    # Helper function to convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Nob Hill at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Presidio at: {to_time(d_val + nobhill_to_presidio)} (travel time = {nobhill_to_presidio} minutes)")
    print(f"  Meeting with Timothy starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Timothy ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")