from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Nob Hill (in minutes after 9:00AM)
#   m_start: meeting start time at Pacific Heights (in minutes after 9:00AM)
#   m_end: meeting end time at Pacific Heights (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Nob Hill to Pacific Heights is 8 minutes.
nobhill_to_pacific = 8

# Margaret's availability at Pacific Heights:
# 3:45PM is 6 hours 45 minutes after 9:00AM --> 405 minutes.
# 7:15PM is 10 hours 15 minutes after 9:00AM --> 615 minutes.
margaret_avail_from = 405
margaret_avail_until = 615

# Constraints:

# 1. You arrive at Nob Hill at 9:00AM, so you cannot leave before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival time at Pacific Heights is d + travel time.
arrival_at_pacific = d + nobhill_to_pacific

# 3. You can only start meeting after arriving at Pacific Heights and after Margaret is available.
opt.add(m_start >= arrival_at_pacific)
opt.add(m_start >= margaret_avail_from)

# 4. The meeting must finish by the time Margaret's availability ends.
opt.add(m_end <= margaret_avail_until)

# 5. You'd like to meet Margaret for a minimum of 45 minutes.
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

    # Helper function: convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Nob Hill at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Pacific Heights at: {to_time(d_val + nobhill_to_pacific)} (travel time = {nobhill_to_pacific} minutes)")
    print(f"  Meeting with Margaret starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Margaret ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")