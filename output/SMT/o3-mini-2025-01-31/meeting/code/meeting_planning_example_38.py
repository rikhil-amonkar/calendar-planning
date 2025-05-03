from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Union Square (minutes after 9:00AM)
#   m_start: meeting start time at North Beach (minutes after 9:00AM)
#   m_end: meeting end time at North Beach (minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Union Square to North Beach is 10 minutes.
us_to_nb = 10

# Margaret's availability at North Beach:
# 9:45PM is 12 hours 45 minutes after 9:00AM -> 765 minutes.
# 10:30PM is 13 hours 30 minutes after 9:00AM -> 810 minutes.
margaret_avail_from = 765
margaret_avail_until = 810

# Constraints:

# 1. You arrive at Union Square at 9:00AM so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 10 minutes to travel from Union Square to North Beach.
arrival_at_nb = d + us_to_nb

# 3. Your meeting with Margaret cannot start until you have arrived at North Beach and 
#    not before Margaret is available.
opt.add(m_start >= arrival_at_nb)
opt.add(m_start >= margaret_avail_from)

# 4. Margaret is available until 10:30PM.
opt.add(m_end <= margaret_avail_until)

# 5. You'd like to meet Margaret for at least 45 minutes.
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
    
    # Helper function to convert minutes after 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Union Square at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at North Beach at: {to_time(d_val + us_to_nb)} (travel time = {us_to_nb} minutes)")
    print(f"  Meeting with Margaret starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Margaret ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")