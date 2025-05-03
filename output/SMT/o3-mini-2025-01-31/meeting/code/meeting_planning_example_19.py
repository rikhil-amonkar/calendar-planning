from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Golden Gate Park (in minutes after 9:00AM)
#   m_start: meeting start time at Pacific Heights (in minutes after 9:00AM)
#   m_end: meeting end time at Pacific Heights (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Golden Gate Park to Pacific Heights is 16 minutes.
ggp_to_pacific = 16

# John's availability at Pacific Heights:
# 7:45PM relative to 9:00AM: 7:45PM is 10 hours 45 minutes after 9:00AM = 645 minutes.
# 8:45PM relative to 9:00AM: 8:45PM is 11 hours 45 minutes after 9:00AM = 705 minutes.
john_arrival = 645
john_departure = 705

# Constraints:
# 1. You arrive at Golden Gate Park at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. After departing, travel time from Golden Gate Park to Pacific Heights takes 16 minutes.
arrival_at_pacific = d + ggp_to_pacific

# 3. The meeting cannot start until you have arrived at Pacific Heights and until John is available.
opt.add(m_start >= arrival_at_pacific)
opt.add(m_start >= john_arrival)

# 4. John is available until 8:45PM.
opt.add(m_end <= john_departure)

# 5. You'd like to meet John for a minimum of 45 minutes.
opt.add(m_end - m_start >= 45)

# Objective: Maximize the meeting duration (even though the window is fixed,
# the optimizer will choose the latest possible end time and earliest start time within the constraints).
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
        # Adjust for 24-hour time if needed, though here it's within the same day.
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Golden Gate Park at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Pacific Heights at: {to_time(d_val + ggp_to_pacific)} (travel time = {ggp_to_pacific} minutes)")
    print(f"  Meeting with John starts at: {to_time(m_start_val)}")
    print(f"  Meeting with John ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")