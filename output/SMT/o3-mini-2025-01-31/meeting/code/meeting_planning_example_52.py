from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Russian Hill (in minutes after 9:00AM)
#   m_start: meeting start time at Richmond District (in minutes after 9:00AM)
#   m_end: meeting end time at Richmond District (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Russian Hill to Richmond District is 14 minutes.
russianhill_to_richmond = 14

# Barbara's availability at Richmond District:
# From 1:15PM to 6:15PM.
# 1:15PM is 4 hours 15 minutes after 9:00AM = 255 minutes.
# 6:15PM is 9 hours 15 minutes after 9:00AM = 555 minutes.
barbara_avail_from = 255
barbara_avail_until = 555

# Constraints:

# 1. You arrive at Russian Hill at 9:00AM so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Departure plus travel time gives the arrival time at Richmond District.
arrival_at_richmond = d + russianhill_to_richmond

# 3. The meeting with Barbara cannot start until you've arrived at Richmond District
#    and not before her availability begins.
opt.add(m_start >= arrival_at_richmond)
opt.add(m_start >= barbara_avail_from)

# 4. The meeting must end by Barbara's availability end time.
opt.add(m_end <= barbara_avail_until)

# 5. You'd like to meet Barbara for a minimum of 45 minutes.
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
    print(f"  Depart Russian Hill at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Richmond District at: {to_time(d_val + russianhill_to_richmond)} (travel time = {russianhill_to_richmond} minutes)")
    print(f"  Meeting with Barbara starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Barbara ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")