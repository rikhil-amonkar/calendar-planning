from z3 import Optimize, Int, sat

# Create the optimizer instance.
opt = Optimize()

# All times measured in minutes after 9:00AM.
# Variables:
#   d: departure time from North Beach (in minutes after 9:00AM)
#   m_start: meeting start time at Nob Hill (in minutes after 9:00AM)
#   m_end: meeting end time at Nob Hill (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from North Beach to Nob Hill is 7 minutes.
nb_to_nobhill = 7

# Melissa's availability at Nob Hill:
# Available from 9:30AM to 8:30PM.
# 9:30AM corresponds to 30 minutes after 9:00AM.
# 8:30PM corresponds to 11.5 hours after 9:00AM -> 11.5 * 60 = 690 minutes.
melissa_avail_from = 30
melissa_avail_until = 690

# Constraints:

# 1. You arrive at North Beach at 9:00AM, so departure from North Beach cannot be before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival at Nob Hill is the departure time plus travel time.
arrival_at_nobhill = d + nb_to_nobhill

# 3. The meeting with Melissa can start only after you have arrived at Nob Hill 
#    and not before Melissa is available.
opt.add(m_start >= arrival_at_nobhill)
opt.add(m_start >= melissa_avail_from)

# 4. The meeting must end by the time Melissa's availability ends.
opt.add(m_end <= melissa_avail_until)

# 5. You'd like to meet Melissa for a minimum of 75 minutes.
opt.add(m_end - m_start >= 75)

# Objective: maximize the meeting duration (m_end - m_start).
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the problem.
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
    print(f"  Depart North Beach at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Nob Hill at: {to_time(d_val + nb_to_nobhill)} (travel time = {nb_to_nobhill} minutes)")
    print(f"  Meeting with Melissa starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Melissa ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")