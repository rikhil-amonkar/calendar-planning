from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Golden Gate Park (in minutes after 9:00AM)
#   m_start: meeting start time at North Beach
#   m_end: meeting end time at North Beach
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Golden Gate Park to North Beach is 24 minutes.
ggp_to_nb = 24

# Ronald's availability at North Beach:
# From 9:30AM to 6:30PM.
# 9:30AM is 30 minutes after 9:00AM.
# 6:30PM is 9.5 hours after 9:00AM => 9.5 * 60 = 570 minutes.
ronald_avail_from = 30
ronald_avail_until = 570

# Constraints:

# 1. You arrive at Golden Gate Park at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart from Golden Gate Park at time d, you reach North Beach at:
arrival_at_nb = d + ggp_to_nb
# 3. The meeting with Ronald can start only after you have arrived at North Beach
#    and not before Ronald's availability begins.
opt.add(m_start >= arrival_at_nb)
opt.add(m_start >= ronald_avail_from)

# 4. The meeting must conclude by the end of Ronald's availability.
opt.add(m_end <= ronald_avail_until)

# 5. You'd like to meet Ronald for at least 30 minutes.
opt.add(m_end - m_start >= 30)

# Objective: maximize the meeting duration.
opt.maximize(m_end - m_start)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()

    # Helper: Convert minutes after 9:00AM to HH:MM.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Golden Gate Park at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at North Beach at: {to_time(d_val + ggp_to_nb)} (travel time = {ggp_to_nb} minutes)")
    print(f"  Meeting with Ronald starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Ronald ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")