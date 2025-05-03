from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Union Square (in minutes after 9:00AM)
#   m_start: meeting start time at Chinatown (in minutes after 9:00AM)
#   m_end: meeting end time at Chinatown (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Union Square to Chinatown is 7 minutes.
union_to_chinatown = 7

# Joshua's availability at Chinatown:
# 6:00PM is 540 minutes after 9:00AM.
# 9:30PM is 750 minutes after 9:00AM.
joshua_start = 540
joshua_end = 750

# Constraints:

# 1. You arrive at Union Square at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 7 minutes to travel from Union Square to Chinatown.
arrival_at_chinatown = d + union_to_chinatown

# 3. The meeting with Joshua cannot start until you have arrived at Chinatown 
#    and until Joshua is available.
opt.add(m_start >= arrival_at_chinatown)
opt.add(m_start >= joshua_start)

# 4. Joshua is available until 9:30PM.
opt.add(m_end <= joshua_end)

# 5. You'd like to meet Joshua for a minimum of 75 minutes.
opt.add(m_end - m_start >= 75)

# Objective: maximize the meeting duration (m_end - m_start)
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
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
    print(f"  Depart Union Square at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Chinatown at: {to_time(d_val + union_to_chinatown)} (travel time = {union_to_chinatown} minutes)")
    print(f"  Meeting with Joshua starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Joshua ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")