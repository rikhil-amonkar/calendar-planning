from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# Time is measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Chinatown (in minutes after 9:00AM)
#   m_start: meeting start time at Nob Hill (in minutes after 9:00AM)
#   m_end: meeting end time at Nob Hill (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time (in minutes):
chinatown_to_nobhill = 8

# Joseph's availability at Nob Hill:
# 11:30AM is 150 minutes after 9:00AM.
# 3:15PM is 375 minutes after 9:00AM.
joseph_arrival = 150
joseph_departure = 375

# Constraints:

# 1. You arrive at Chinatown at 9:00AM so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 8 minutes to travel from Chinatown to Nob Hill.
arrival_at_nobhill = d + chinatown_to_nobhill

# 3. The meeting with Joseph cannot start until you have arrived at Nob Hill
#    and until Joseph is available.
opt.add(m_start >= arrival_at_nobhill)
opt.add(m_start >= joseph_arrival)

# 4. Joseph is available until 3:15PM.
opt.add(m_end <= joseph_departure)

# 5. You'd like to meet Joseph for at least 75 minutes.
opt.add(m_end - m_start >= 75)

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
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Chinatown at: {to_time(d_val)} (9:00AM + {d_val} min)")
    print(f"  Arrive at Nob Hill at: {to_time(d_val + chinatown_to_nobhill)} (travel time = {chinatown_to_nobhill} min)")
    print(f"  Meeting with Joseph starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Joseph ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")