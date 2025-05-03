from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from Presidio (in minutes after 9:00AM)
#   m_start : meeting start time at Golden Gate Park (in minutes after 9:00AM)
#   m_end   : meeting end time at Golden Gate Park (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Presidio to Golden Gate Park is 12 minutes.
presidio_to_ggp = 12

# Carol's availability at Golden Gate Park:
# Carol is there from 9:45PM to 10:30PM.
# Relative to 9:00AM, 9:45PM is 765 minutes and 10:30PM is 810 minutes.
carol_avail_from = 765
carol_avail_until = 810

# CONSTRAINTS:

# 1. You arrive at Presidio at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Arrival time at Golden Gate Park is your departure time plus travel time.
arrival_at_ggp = d + presidio_to_ggp

# 3. The meeting with Carol cannot start before you arrive at Golden Gate Park
#    and cannot start before Carol is available.
opt.add(m_start >= arrival_at_ggp)
opt.add(m_start >= carol_avail_from)

# 4. The meeting must end by the time Carol's availability ends.
opt.add(m_end <= carol_avail_until)

# 5. You'd like to meet Carol for at least 45 minutes.
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
    print(f"  Depart Presidio at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Golden Gate Park at: {to_time(d_val + presidio_to_ggp)} (travel time = {presidio_to_ggp} minutes)")
    print(f"  Meeting with Carol starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Carol ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")