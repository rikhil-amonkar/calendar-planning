from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from North Beach (in minutes after 9:00AM)
#   m_start : meeting start time at Bayview (in minutes after 9:00AM)
#   m_end   : meeting end time at Bayview (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from North Beach to Bayview is 22 minutes.
nb_to_bayview = 22

# Steven's availability at Bayview:
# 11:00AM is 120 minutes after 9:00AM.
# 12:45PM is 225 minutes after 9:00AM.
steven_avail_from = 120
steven_avail_until = 225

# CONSTRAINTS:

# 1. You arrive at North Beach at 9:00AM so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart from North Beach at time d,
#    you will arrive at Bayview at: d + nb_to_bayview.
arrival_at_bayview = d + nb_to_bayview

# 3. The meeting with Steven cannot start before you arrive at Bayview,
#    and it cannot start before his availability begins.
opt.add(m_start >= arrival_at_bayview)
opt.add(m_start >= steven_avail_from)

# 4. The meeting must end by the time Steven's availability ends.
opt.add(m_end <= steven_avail_until)

# 5. You'd like to meet Steven for at least 90 minutes.
opt.add(m_end - m_start >= 90)

# Objective: Maximize the meeting duration (if possible).
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper: Convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart North Beach at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Bayview at: {to_time(d_val + nb_to_bayview)} (travel time = {nb_to_bayview} minutes)")
    print(f"  Meeting with Steven starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Steven ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")