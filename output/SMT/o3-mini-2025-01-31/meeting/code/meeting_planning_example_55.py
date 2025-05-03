from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Financial District (in minutes after 9:00AM)
#   m_start: meeting start time at Nob Hill (in minutes after 9:00AM)
#   m_end: meeting end time at Nob Hill (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Financial District to Nob Hill is 8 minutes.
fd_to_nobhill = 8

# Helen's availability at Nob Hill:
# 11:30AM is 150 minutes after 9:00AM.
# 12:15PM is 195 minutes after 9:00AM.
helen_avail_from = 150
helen_avail_until = 195

# Constraints:

# 1. You arrive at Financial District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. The arrival time at Nob Hill is the departure time plus travel time.
arrival_at_nobhill = d + fd_to_nobhill

# 3. The meeting with Helen can only start after you have arrived at Nob Hill 
#    and not before Helen is available.
opt.add(m_start >= arrival_at_nobhill)
opt.add(m_start >= helen_avail_from)

# 4. The meeting must end by the time Helen's availability ends.
opt.add(m_end <= helen_avail_until)

# 5. You'd like to meet Helen for a minimum of 45 minutes.
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
    print(f"  Depart Financial District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Nob Hill at: {to_time(d_val + fd_to_nobhill)} (travel time = {fd_to_nobhill} minutes)")
    print(f"  Meeting with Helen starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Helen ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")