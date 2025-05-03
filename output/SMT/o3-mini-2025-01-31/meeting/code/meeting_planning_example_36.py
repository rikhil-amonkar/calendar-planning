from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#  d: departure time from Marina District (in minutes after 9:00AM)
#  m_start: meeting start time at Embarcadero (in minutes after 9:00AM)
#  m_end: meeting end time at Embarcadero (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Travel time from Marina District to Embarcadero is 14 minutes.
marina_to_embarcadero = 14

# Barbara's availability at Embarcadero:
# 1:30PM is 4 hours and 30 minutes after 9:00AM -> 270 minutes after 9:00AM.
# 8:45PM is 11 hours and 45 minutes after 9:00AM -> 705 minutes after 9:00AM.
barbara_available_from = 270
barbara_available_until = 705

# Constraints:
# 1. You arrive at Marina District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. You travel from Marina District to Embarcadero in 14 minutes.
arrival_at_embarcadero = d + marina_to_embarcadero

# 3. The meeting with Barbara cannot start until you have arrived at Embarcadero
#    and not before Barbara is available.
opt.add(m_start >= arrival_at_embarcadero)
opt.add(m_start >= barbara_available_from)

# 4. Barbara is available until 8:45PM.
opt.add(m_end <= barbara_available_until)

# 5. You'd like to meet Barbara for a minimum of 60 minutes.
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
    
    # Helper function to convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Marina District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Embarcadero at: {to_time(d_val + marina_to_embarcadero)} (travel time = {marina_to_embarcadero} minutes)")
    print(f"  Meeting with Barbara starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Barbara ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")