from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Financial District (in minutes after 9:00AM)
#   m_start: meeting start time at Union Square (in minutes after 9:00AM)
#   m_end: meeting end time at Union Square (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Financial District to Union Square is 9 minutes.
fd_to_us = 9

# Joseph's availability at Union Square:
# 9:30PM is 750 minutes after 9:00AM (12.5 hours later).
# 10:00PM is 780 minutes after 9:00AM.
joseph_avail_from = 750
joseph_avail_until = 780

# Constraints:

# 1. You arrive at Financial District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 9 minutes to travel from Financial District to Union Square.
arrival_at_us = d + fd_to_us

# 3. The meeting with Joseph can only start once you've arrived at Union Square,
#    and cannot begin before Joseph's availability starts.
opt.add(m_start >= arrival_at_us)
opt.add(m_start >= joseph_avail_from)

# 4. The meeting must end by the time Joseph's availability ends.
opt.add(m_end <= joseph_avail_until)

# 5. You'd like to meet Joseph for a minimum of 15 minutes.
opt.add(m_end - m_start >= 15)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the problem.
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
    print(f"  Depart Financial District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Union Square at: {to_time(d_val + fd_to_us)} (travel time = {fd_to_us} minutes)")
    print(f"  Meeting with Joseph starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Joseph ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")