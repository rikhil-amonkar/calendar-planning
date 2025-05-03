from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Richmond District (in minutes after 9:00AM)
#   m_start: meeting start time at Presidio (in minutes after 9:00AM)
#   m_end: meeting end time at Presidio (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Richmond District to Presidio is 7 minutes.
richmond_to_presidio = 7

# Sarah's availability at Presidio:
# 1:15PM is 255 minutes after 9:00AM.
# 3:15PM is 375 minutes after 9:00AM.
sarah_start = 255
sarah_end = 375

# Constraints:
# 1. You arrive at Richmond District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 7 minutes to travel from Richmond District to Presidio.
arrival_at_presidio = d + richmond_to_presidio

# 3. The meeting with Sarah cannot start until after you have arrived at Presidio 
#    and not before Sarah is available.
opt.add(m_start >= arrival_at_presidio)
opt.add(m_start >= sarah_start)

# 4. Sarah is available until 3:15PM.
opt.add(m_end <= sarah_end)

# 5. You'd like to meet Sarah for a minimum of 105 minutes.
opt.add(m_end - m_start >= 105)

# Objective: maximize the meeting duration (m_end - m_start).
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
    print(f"  Depart Richmond District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Presidio at: {to_time(d_val + richmond_to_presidio)} (travel time = {richmond_to_presidio} minutes)")
    print(f"  Meeting with Sarah starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Sarah ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")