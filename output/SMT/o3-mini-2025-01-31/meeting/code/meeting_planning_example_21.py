from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Mission District (in minutes after 9:00AM)
#   m_start: meeting start time at Haight-Ashbury (in minutes after 9:00AM)
#   m_end: meeting end time at Haight-Ashbury (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Mission District to Haight-Ashbury is 12 minutes.
mission_to_haight = 12

# Margaret's availability at Haight-Ashbury:
# Available from 8:00AM to 3:45PM.
# 8:00AM is 60 minutes before 9:00AM: -60 minutes after 9:00AM.
# 3:45PM is 6 hours 45 minutes after 9:00AM: 405 minutes.
margaret_available_from = -60
margaret_available_until = 405

# Constraints:

# 1. You arrive at Mission District at 9:00AM.
#    Hence, you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. After departing Mission District, you need 12 minutes to reach Haight-Ashbury.
arrival_at_haight = d + mission_to_haight

# 3. The meeting cannot start before you have arrived at Haight-Ashbury.
opt.add(m_start >= arrival_at_haight)

# Additionally, Margaret is available starting at 8:00AM, 
# so the meeting start must be no earlier than her availability.
opt.add(m_start >= margaret_available_from)

# 4. Margaret is available until 3:45PM.
opt.add(m_end <= margaret_available_until)

# 5. You'd like to meet Margaret for at least 30 minutes.
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
    print(f"  Depart Mission District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Haight-Ashbury at: {to_time(d_val + mission_to_haight)} (travel time = {mission_to_haight} minutes)")
    print(f"  Meeting with Margaret starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Margaret ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")