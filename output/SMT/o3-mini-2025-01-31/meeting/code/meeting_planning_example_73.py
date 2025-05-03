from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Russian Hill (in minutes after 9:00AM)
#   m_start: meeting start time at Pacific Heights (in minutes after 9:00AM)
#   m_end: meeting end time at Pacific Heights (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Russian Hill to Pacific Heights is 7 minutes.
rh_to_ph = 7

# Barbara's availability at Pacific Heights:
# She is available from 7:15AM to 10:00PM.
# Relative to 9:00AM: 7:15AM is -105 minutes and 10:00PM is 780 minutes.
barbara_avail_from = -105
barbara_avail_until = 780

# CONSTRAINTS:

# 1. You arrive at Russian Hill at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart Russian Hill at time d, you arrive at Pacific Heights after travel.
arrival_at_ph = d + rh_to_ph

# 3. The meeting with Barbara can only start after you have arrived at Pacific Heights 
#    and not before Barbara is available.
opt.add(m_start >= arrival_at_ph)
opt.add(m_start >= barbara_avail_from)

# 4. The meeting must end by the time Barbara's availability ends.
opt.add(m_end <= barbara_avail_until)

# 5. You'd like to meet Barbara for at least 60 minutes.
opt.add(m_end - m_start >= 60)

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
    print(f"  Depart Russian Hill at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Pacific Heights at: {to_time(d_val + rh_to_ph)} (travel time = {rh_to_ph} minutes)")
    print(f"  Meeting with Barbara starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Barbara ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")