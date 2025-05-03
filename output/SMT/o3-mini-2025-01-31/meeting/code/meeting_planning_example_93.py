from z3 import Optimize, Int, sat

# Create the optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from North Beach (in minutes after 9:00AM)
#   m_start : meeting start time at Chinatown (in minutes after 9:00AM)
#   m_end   : meeting end time at Chinatown (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from North Beach to Chinatown is 6 minutes.
nb_to_chinatown = 6

# Emily's availability at Chinatown:
# 7:00PM is 600 minutes after 9:00AM (10 hours later).
# 9:00PM is 720 minutes after 9:00AM (12 hours later).
emily_avail_from = 600
emily_avail_until = 720

# CONSTRAINTS:

# 1. You arrive at North Beach at 9:00AM, so you cannot depart before then.
opt.add(d >= 0)

# 2. When you depart from North Beach at time d, you arrive at Chinatown at:
arrival_at_chinatown = d + nb_to_chinatown

# 3. The meeting with Emily cannot start before you arrive at Chinatown, 
#    and cannot start before Emily's availability begins.
opt.add(m_start >= arrival_at_chinatown)
opt.add(m_start >= emily_avail_from)

# 4. The meeting must be finished by the time Emily's availability ends.
opt.add(m_end <= emily_avail_until)

# 5. You'd like to meet Emily for at least 75 minutes.
opt.add(m_end - m_start >= 75)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function to convert minutes after 9:00AM into a HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart North Beach at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Chinatown at: {to_time(d_val + nb_to_chinatown)} (travel time = {nb_to_chinatown} minutes)")
    print(f"  Meeting with Emily starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Emily ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")