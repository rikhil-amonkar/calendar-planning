from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from North Beach (in minutes after 9:00AM)
#   m_start: meeting start time at Haight-Ashbury (in minutes after 9:00AM)
#   m_end: meeting end time at Haight-Ashbury (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from North Beach to Haight-Ashbury is 18 minutes.
northbeach_to_haight = 18

# George's availability at Haight-Ashbury:
# From 7:30AM to 1:15PM.
# 7:30AM is 90 minutes before 9:00AM, i.e., -90 minutes.
# 1:15PM is 4 hours 15 minutes after 9:00AM, i.e., 255 minutes.
george_avail_from = -90
george_avail_until = 255

# Constraints:
# 1. You arrive at North Beach at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 18 minutes to travel from North Beach to Haight-Ashbury.
arrival_at_haight = d + northbeach_to_haight

# 3. The meeting with George cannot start until you have arrived at Haight-Ashbury.
# Also, George is already available from 7:30AM, so meeting starts no earlier than his available time.
opt.add(m_start >= arrival_at_haight)
opt.add(m_start >= george_avail_from)

# 4. George is available until 1:15PM.
opt.add(m_end <= george_avail_until)

# 5. You'd like to meet George for a minimum of 45 minutes.
opt.add(m_end - m_start >= 45)

# Objective: maximize the meeting duration (m_end - m_start).
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function: convert minutes after 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart North Beach at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Haight-Ashbury at: {to_time(d_val + northbeach_to_haight)} (travel time = {northbeach_to_haight} minutes)")
    print(f"  Meeting with George starts at: {to_time(m_start_val)}")
    print(f"  Meeting with George ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")