from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from The Castro (in minutes after 9:00AM)
#   m_start: meeting start time at Golden Gate Park (in minutes after 9:00AM)
#   m_end: meeting end time at Golden Gate Park (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from The Castro to Golden Gate Park is 11 minutes.
castro_to_ggp = 11

# Jeffrey's availability at Golden Gate Park:
# Available from 7:00AM to 5:30PM.
# 7:00AM is 2 hours before 9:00AM, i.e., -120 minutes.
# 5:30PM is 8.5 hours after 9:00AM, i.e., 510 minutes.
jeffrey_available_from = -120
jeffrey_available_until = 510

# Constraints:

# 1. You arrive at The Castro at 9:00AM so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 11 minutes to travel to Golden Gate Park.
arrival_at_ggp = d + castro_to_ggp

# 3. The meeting with Jeffrey cannot start until you have arrived at Golden Gate Park.
# Additionally, Jeffrey is available from 7:00AM, but since you arrive after 9:00AM,
# the meeting can only start once you get there.
opt.add(m_start >= arrival_at_ggp)

# 4. The meeting must end by Jeffrey's departure time at 5:30PM.
opt.add(m_end <= jeffrey_available_until)

# 5. You’d like to meet Jeffrey for at least 105 minutes.
opt.add(m_end - m_start >= 105)

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
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart The Castro at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Golden Gate Park at: {to_time(d_val + castro_to_ggp)} (travel time = {castro_to_ggp} minutes)")
    print(f"  Meeting with Jeffrey starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Jeffrey ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")