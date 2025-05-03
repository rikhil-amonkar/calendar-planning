from z3 import Optimize, Int, sat

# Create the optimizer instance
opt = Optimize()

# All times are represented in minutes after 9:00AM.
# Variables:
#   d       : the departure time from Mission District (in minutes after 9:00AM)
#   m_start : the meeting start time at Bayview (in minutes after 9:00AM)
#   m_end   : the meeting end time at Bayview (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Mission District to Bayview is 15 minutes.
mission_to_bayview = 15

# Patricia's availability at Bayview: from 6:00PM to 7:30PM.
# 6:00PM is 9 hours after 9:00AM -> 9 * 60 = 540 minutes.
# 7:30PM is 10.5 hours after 9:00AM -> 10.5 * 60 = 630 minutes.
patricia_avail_from = 540
patricia_avail_until = 630

# CONSTRAINTS:

# 1. You arrive at Mission District at 9:00AM. You cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart Mission District at time d, you arrive at Bayview at d + mission_to_bayview.
arrival_at_bayview = d + mission_to_bayview

# 3. The meeting with Patricia cannot start before you arrive at Bayview,
#    and cannot start before her availability begins.
opt.add(m_start >= arrival_at_bayview)
opt.add(m_start >= patricia_avail_from)

# 4. The meeting must end by the time Patricia's availability ends.
opt.add(m_end <= patricia_avail_until)

# 5. You'd like to meet Patricia for at least 60 minutes.
opt.add(m_end - m_start >= 60)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()

    # Helper function to convert minutes after 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    print("Optimal Schedule:")
    print(f"  Depart Mission District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Bayview at: {to_time(d_val + mission_to_bayview)} (travel time = {mission_to_bayview} minutes)")
    print(f"  Meeting with Patricia starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Patricia ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")