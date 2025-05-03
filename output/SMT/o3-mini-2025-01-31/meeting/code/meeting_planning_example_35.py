from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Bayview (in minutes after 9:00AM)
#   m_start: meeting start time at Chinatown (in minutes after 9:00AM)
#   m_end: meeting end time at Chinatown (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Bayview to Chinatown is 18 minutes.
bayview_to_chinatown = 18

# Jason's availability at Chinatown:
# From 8:30AM to 12:30PM.
# 8:30AM is 30 minutes before 9:00AM, i.e., -30 minutes.
# 12:30PM is 3.5 hours after 9:00AM, i.e., 210 minutes.
jason_available_from = -30
jason_available_until = 210

# Constraints:

# 1. You arrive at Bayview at 9:00AM so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 18 minutes to travel from Bayview to Chinatown.
arrival_at_chinatown = d + bayview_to_chinatown

# 3. The meeting with Jason cannot start until you have arrived at Chinatown.
# Also, Jason is available starting from 8:30AM, but you'll likely arrive after 9:00AM.
opt.add(m_start >= arrival_at_chinatown)

# 4. The meeting must end by Jason's availability end at 12:30PM.
opt.add(m_end <= jason_available_until)

# 5. You'd like to meet Jason for a minimum of 90 minutes.
opt.add(m_end - m_start >= 90)

# Objective: maximize the meeting duration (m_end - m_start)
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
    print(f"  Depart Bayview at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Chinatown at: {to_time(d_val + bayview_to_chinatown)} (travel time = {bayview_to_chinatown} minutes)")
    print(f"  Meeting with Jason starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Jason ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")