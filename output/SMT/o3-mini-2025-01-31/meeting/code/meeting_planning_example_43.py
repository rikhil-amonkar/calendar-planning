from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Marina District (in minutes after 9:00AM)
#   m_start: meeting start time at Chinatown (in minutes after 9:00AM)
#   m_end: meeting end time at Chinatown (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Marina District to Chinatown is 16 minutes.
marina_to_chinatown = 16

# Sandra's availability at Chinatown:
# Available from 9:00AM to 11:45AM.
# 9:00AM corresponds to 0 minutes after 9:00AM.
# 11:45AM corresponds to 2 hours 45 minutes = 165 minutes after 9:00AM.
sandra_avail_from = 0
sandra_avail_until = 165

# Constraints:

# 1. You arrive at Marina District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 16 minutes to travel from Marina District to Chinatown.
arrival_at_chinatown = d + marina_to_chinatown

# 3. The meeting with Sandra cannot start until you've arrived at Chinatown
#    and not before Sandra is available.
opt.add(m_start >= arrival_at_chinatown)
opt.add(m_start >= sandra_avail_from)

# 4. The meeting must end by Sandra's availability end time.
opt.add(m_end <= sandra_avail_until)

# 5. You'd like to meet Sandra for a minimum of 15 minutes.
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
    
    # Helper function: convert minutes after 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Marina District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Chinatown at: {to_time(d_val + marina_to_chinatown)} (travel time = {marina_to_chinatown} minutes)")
    print(f"  Meeting with Sandra starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Sandra ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")