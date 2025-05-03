from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes relative to 9:00AM.
# Variables:
#   d: departure time from The Castro (in minutes after 9:00AM)
#   m_start: meeting start time at Embarcadero (in minutes after 9:00AM)
#   m_end: meeting end time at Embarcadero (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from The Castro to Embarcadero is 22 minutes.
castro_to_embarcadero = 22

# Laura's availability at Embarcadero:
# From 8:00AM to 11:00AM.
# Since times are relative to 9:00AM, 8:00AM becomes -60 minutes
# and 11:00AM becomes 120 minutes.
laura_avail_from = -60
laura_avail_until = 120

# Constraints:

# 1. You arrive at The Castro at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 22 minutes to travel from The Castro to Embarcadero.
arrival_at_embarcadero = d + castro_to_embarcadero

# 3. The meeting with Laura can only start after you've arrived at Embarcadero
#    and not before Laura's availability begins.
opt.add(m_start >= arrival_at_embarcadero)
opt.add(m_start >= laura_avail_from)

# 4. The meeting must end by the time Laura's availability ends.
opt.add(m_end <= laura_avail_until)

# 5. You'd like to meet Laura for a minimum of 15 minutes.
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
    
    # Helper function to convert minutes relative to 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart The Castro at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Embarcadero at: {to_time(d_val + castro_to_embarcadero)} (travel time = {castro_to_embarcadero} minutes)")
    print(f"  Meeting with Laura starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Laura ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")