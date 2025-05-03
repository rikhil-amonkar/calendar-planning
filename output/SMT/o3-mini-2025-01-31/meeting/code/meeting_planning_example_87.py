from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from Embarcadero (in minutes after 9:00AM)
#   m_start : meeting start time at Pacific Heights (in minutes after 9:00AM)
#   m_end   : meeting end time at Pacific Heights (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Embarcadero to Pacific Heights is 11 minutes.
emb_to_ph = 11

# James's availability at Pacific Heights:
# 8:30AM is 30 minutes before 9:00AM, i.e., -30 minutes relative to 9:00AM.
# 3:00PM is 6 hours after 9:00AM, i.e., 360 minutes.
james_avail_from = -30
james_avail_until = 360

# CONSTRAINTS:

# 1. You arrive at Embarcadero at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart from Embarcadero at time d, you arrive at Pacific Heights after emb_to_ph minutes.
arrival_at_ph = d + emb_to_ph

# 3. The meeting with James cannot start before you arrive at Pacific Heights
#    and cannot start before his availability begins.
opt.add(m_start >= arrival_at_ph)
opt.add(m_start >= james_avail_from)

# 4. The meeting must end by the time James's availability ends.
opt.add(m_end <= james_avail_until)

# 5. You'd like to meet James for at least 75 minutes.
opt.add(m_end - m_start >= 75)

# Objective: maximize the meeting duration (m_end - m_start).
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
    print(f"  Depart Embarcadero at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Pacific Heights at: {to_time(d_val + emb_to_ph)} (travel time = {emb_to_ph} minutes)")
    print(f"  Meeting with James starts at: {to_time(m_start_val)}")
    print(f"  Meeting with James ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")