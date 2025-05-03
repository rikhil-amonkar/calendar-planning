from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Nob Hill (in minutes after 9:00AM)
#   m_start: meeting start time at Alamo Square (in minutes after 9:00AM)
#   m_end: meeting end time at Alamo Square (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Nob Hill to Alamo Square is 11 minutes.
nobhill_to_alamo = 11

# Anthony's availability at Alamo Square:
# Available from 7:15AM to 1:00PM.
# 7:15AM relative to 9:00AM is -105 minutes.
# 1:00PM relative to 9:00AM is 240 minutes.
anthony_available_from = -105
anthony_available_until = 240

# Constraints:

# 1. You arrive at Nob Hill at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 11 minutes to travel from Nob Hill to Alamo Square.
arrival_at_alamo = d + nobhill_to_alamo

# 3. The meeting with Anthony cannot start until you have arrived at Alamo Square.
# Although Anthony is available from 7:15AM, you'll arrive after 9:00AM.
opt.add(m_start >= arrival_at_alamo)

# 4. Anthony is available until 1:00PM (i.e., 240 minutes after 9:00AM).
opt.add(m_end <= anthony_available_until)

# 5. You'd like to meet Anthony for a minimum of 15 minutes.
opt.add(m_end - m_start >= 15)

# Objective: maximize the meeting duration
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
    print(f"  Depart Nob Hill at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Alamo Square at: {to_time(d_val + nobhill_to_alamo)} (travel time = {nobhill_to_alamo} minutes)")
    print(f"  Meeting with Anthony starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Anthony ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")