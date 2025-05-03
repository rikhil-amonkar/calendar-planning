from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Fisherman's Wharf (minutes after 9:00AM)
#   m_start: meeting start time at Nob Hill (minutes after 9:00AM)
#   m_end: meeting end time at Nob Hill (minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Fisherman's Wharf to Nob Hill is 11 minutes.
wharf_to_nobhill = 11

# Stephanie's availability at Nob Hill:
# 4:45PM is 465 minutes after 9:00AM, and 9:45PM is 765 minutes after 9:00AM.
stephanie_avail_from = 465
stephanie_avail_until = 765

# Constraints:

# 1. You arrive at Fisherman's Wharf at 9:00AM so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 11 minutes to travel from Fisherman's Wharf to Nob Hill.
arrival_at_nobhill = d + wharf_to_nobhill

# 3. The meeting with Stephanie cannot start until you've arrived at Nob Hill
#    and not before Stephanie's availability begins.
opt.add(m_start >= arrival_at_nobhill)
opt.add(m_start >= stephanie_avail_from)

# 4. The meeting must end by Stephanie's availability end time.
opt.add(m_end <= stephanie_avail_until)

# 5. You'd like to meet Stephanie for a minimum of 120 minutes.
opt.add(m_end - m_start >= 120)

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
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Fisherman's Wharf at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Nob Hill at: {to_time(d_val + wharf_to_nobhill)} (travel time = {wharf_to_nobhill} minutes)")
    print(f"  Meeting with Stephanie starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Stephanie ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")