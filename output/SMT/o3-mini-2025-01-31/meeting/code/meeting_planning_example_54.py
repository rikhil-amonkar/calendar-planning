from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Financial District (in minutes after 9:00AM)
#   m_start: meeting start time at Mission District (in minutes after 9:00AM)
#   m_end: meeting end time at Mission District (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Financial District to Mission District is 17 minutes.
fd_to_mission = 17

# William's availability at Mission District:
# From 1:15PM to 2:15PM.
# 1:15PM = 4 hours 15 minutes after 9:00AM = 255 minutes.
# 2:15PM = 5 hours 15 minutes after 9:00AM = 315 minutes.
william_avail_from = 255
william_avail_until = 315

# Constraints:

# 1. You arrive at Financial District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Travel time: arrival at Mission District is given by:
arrival_at_mission = d + fd_to_mission

# 3. The meeting with William can only start after you have arrived at Mission District
#    and not before his availability begins.
opt.add(m_start >= arrival_at_mission)
opt.add(m_start >= william_avail_from)

# 4. The meeting must end by the time William's availability ends.
opt.add(m_end <= william_avail_until)

# 5. You'd like to meet William for a minimum of 45 minutes.
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
    print(f"  Depart Financial District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Mission District at: {to_time(d_val + fd_to_mission)} (travel time = {fd_to_mission} minutes)")
    print(f"  Meeting with William starts at: {to_time(m_start_val)}")
    print(f"  Meeting with William ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")