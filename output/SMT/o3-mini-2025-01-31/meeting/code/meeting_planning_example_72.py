from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Pacific Heights (in minutes after 9:00AM)
#   m_start: meeting start time at Alamo Square (in minutes after 9:00AM)
#   m_end: meeting end time at Alamo Square (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Pacific Heights to Alamo Square is 10 minutes.
pac_heights_to_alamo = 10

# John's availability at Alamo Square:
# 9:45AM -> 45 minutes after 9:00AM.
# 2:30PM -> 9:00AM + 5.5 hours = 330 minutes.
john_avail_from = 45
john_avail_until = 330

# Constraint 1: You are at Pacific Heights at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# When you depart Pacific Heights, you arrive at Alamo Square at:
arrival_at_alamo = d + pac_heights_to_alamo

# Constraint 2: The meeting with John cannot start before you arrive at Alamo Square,
# and it cannot start before John's availability begins.
opt.add(m_start >= arrival_at_alamo)
opt.add(m_start >= john_avail_from)

# Constraint 3: The meeting must end by the time John's availability ends.
opt.add(m_end <= john_avail_until)

# Constraint 4: You'd like to meet John for at least 90 minutes.
opt.add(m_end - m_start >= 90)

# For optimization, maximize the meeting duration.
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
    print(f"  Depart Pacific Heights at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Alamo Square at: {to_time(d_val + pac_heights_to_alamo)} (travel time = {pac_heights_to_alamo} minutes)")
    print(f"  Meeting with John starts at: {to_time(m_start_val)}")
    print(f"  Meeting with John ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")