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

# Robert's availability at Presidio:
# From 11:15AM to 5:45PM.
# 11:15AM is 2 hours 15 minutes after 9:00AM, i.e., 135 minutes.
# 5:45PM is 8 hours 45 minutes after 9:00AM, i.e., 525 minutes.
robert_avail_from = 135
robert_avail_until = 525

# Constraints:

# 1. You arrive at Nob Hill at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival time at Presidio is your departure time plus the travel time.
arrival_at_presidio = d + nobhill_to_presidio

# 3. The meeting with Robert can begin only after you have arrived at Presidio,
#    and not before Robert is available.
opt.add(m_start >= arrival_at_presidio)
opt.add(m_start >= robert_avail_from)

# 4. The meeting must finish by the time Robert's availability ends.
opt.add(m_end <= robert_avail_until)

# 5. You'd like to meet Robert for a minimum of 120 minutes.
opt.add(m_end - m_start >= 120)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function: Convert minutes after 9:00AM to a HH:MM string.
    def to_time(minutes_after_9):
        total_minutes = 9*60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Nob Hill at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Presidio at: {to_time(d_val + nobhill_to_presidio)} (travel time = {nobhill_to_presidio} minutes)")
    print(f"  Meeting with Robert starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Robert ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")