from z3 import Optimize, Int, sat

# Create the optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from North Beach (in minutes after 9:00AM)
#   m_start : meeting start time at Russian Hill (in minutes after 9:00AM)
#   m_end   : meeting end time at Russian Hill (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from North Beach to Russian Hill is 4 minutes.
nb_to_rh = 4

# William's availability at Russian Hill:
# William is available from 1:15PM to 9:30PM.
# 1:15PM is 4 hours and 15 minutes after 9:00AM -> 4*60 + 15 = 255 minutes.
# 9:30PM is 12.5 hours after 9:00AM -> 12*60 + 30 = 750 minutes.
william_avail_from = 255
william_avail_until = 750

# CONSTRAINTS:

# 1. You arrive at North Beach at 9:00AM, hence you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart North Beach at time d, you arrive at Russian Hill after nb_to_rh minutes.
arrival_at_rh = d + nb_to_rh

# 3. The meeting with William cannot start before you arrive at Russian Hill 
#    and cannot start before his availability begins.
opt.add(m_start >= arrival_at_rh)
opt.add(m_start >= william_avail_from)

# 4. The meeting must end by the time William's availability ends.
opt.add(m_end <= william_avail_until)

# 5. You'd like to meet William for at least 15 minutes.
opt.add(m_end - m_start >= 15)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function: Convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart North Beach at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Russian Hill at: {to_time(d_val + nb_to_rh)} (travel time = {nb_to_rh} minutes)")
    print(f"  Meeting with William starts at: {to_time(m_start_val)}")
    print(f"  Meeting with William ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")