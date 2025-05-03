from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Golden Gate Park
#   m_start: meeting start time at Embarcadero
#   m_end: meeting end time at Embarcadero
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Golden Gate Park to Embarcadero is 25 minutes.
ggp_to_embarcadero = 25

# Sandra's availability at Embarcadero:
# 7:00PM is 600 minutes after 9:00AM (10 hours later).
# 9:00PM is 720 minutes after 9:00AM.
sandra_avail_from = 600
sandra_avail_until = 720

# Constraints:

# 1. You arrive at Golden Gate Park at 9:00AM, so your departure time cannot be before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival time at Embarcadero is your departure time plus the travel time.
arrival_at_embarcadero = d + ggp_to_embarcadero

# 3. The meeting with Sandra can only start after you have arrived at Embarcadero
#    and not before Sandra is available.
opt.add(m_start >= arrival_at_embarcadero)
opt.add(m_start >= sandra_avail_from)

# 4. The meeting must end by the time Sandra's availability ends.
opt.add(m_end <= sandra_avail_until)

# 5. You'd like to meet Sandra for a minimum of 45 minutes.
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
    print(f"  Depart Golden Gate Park at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Embarcadero at: {to_time(d_val + ggp_to_embarcadero)} (travel time = {ggp_to_embarcadero} minutes)")
    print(f"  Meeting with Sandra starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Sandra ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")