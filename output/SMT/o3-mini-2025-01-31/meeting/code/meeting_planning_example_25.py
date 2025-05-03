from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Golden Gate Park (in minutes after 9:00AM)
#   m_start: meeting start time at Chinatown (in minutes after 9:00AM)
#   m_end: meeting end time at Chinatown (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Golden Gate Park to Chinatown is 23 minutes.
ggp_to_chinatown = 23

# David's availability at Chinatown:
# 4:00PM is 7 hours after 9:00AM => 420 minutes.
# 9:45PM is 12 hours 45 minutes after 9:00AM => 765 minutes.
david_start = 420
david_end = 765

# Constraints:
# 1. You arrive at Golden Gate Park at 9:00AM,
#    so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Travel from Golden Gate Park to Chinatown takes 23 minutes.
arrival_at_chinatown = d + ggp_to_chinatown

# 3. Your meeting with David cannot start until you have arrived at Chinatown
#    and until David is available.
opt.add(m_start >= arrival_at_chinatown)
opt.add(m_start >= david_start)

# 4. David is available until 9:45PM.
opt.add(m_end <= david_end)

# 5. You'd like to meet David for at least 105 minutes.
opt.add(m_end - m_start >= 105)

# Objective: Maximize the meeting duration.
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
    print(f"  Depart Golden Gate Park at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Chinatown at: {to_time(d_val + ggp_to_chinatown)} (travel time = {ggp_to_chinatown} minutes)")
    print(f"  Meeting with David starts at: {to_time(m_start_val)}")
    print(f"  Meeting with David ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")