from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Sunset District (minutes after 9:00AM)
#   m_start: meeting start time at Haight-Ashbury (minutes after 9:00AM)
#   m_end: meeting end time at Haight-Ashbury (minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Sunset District to Haight-Ashbury is 15 minutes.
sunset_to_haight = 15

# Nancy's availability at Haight-Ashbury:
# 7:30PM is 10.5 hours after 9:00AM -> 10.5 * 60 = 630 minutes.
# 9:45PM is 12 hours 45 minutes after 9:00AM -> 765 minutes.
nancy_available_from = 630
nancy_available_until = 765

# Constraints:

# 1. You arrive at Sunset District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 15 minutes to travel from Sunset District to Haight-Ashbury.
arrival_at_haight = d + sunset_to_haight

# 3. The meeting with Nancy cannot start until you have reached Haight-Ashbury
#    and until Nancy is available.
opt.add(m_start >= arrival_at_haight)
opt.add(m_start >= nancy_available_from)

# 4. Nancy is available until 9:45PM.
opt.add(m_end <= nancy_available_until)

# 5. You'd like to meet Nancy for a minimum of 75 minutes.
opt.add(m_end - m_start >= 75)

# Objective: Maximize the meeting duration.
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
    print(f"  Depart Sunset District at: {to_time(d_val)} (9:00AM + {d_val} min)")
    print(f"  Arrive at Haight-Ashbury at: {to_time(d_val + sunset_to_haight)} (travel time = {sunset_to_haight} min)")
    print(f"  Meeting with Nancy starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Nancy ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")