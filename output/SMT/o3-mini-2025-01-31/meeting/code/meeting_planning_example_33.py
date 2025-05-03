from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Sunset District (in minutes after 9:00AM)
#   m_start: meeting start time at Union Square (in minutes after 9:00AM)
#   m_end: meeting end time at Union Square (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Sunset District to Union Square is 30 minutes.
sunset_to_union = 30

# Sarah's availability at Union Square:
# 12:30PM is 210 minutes after 9:00AM.
# 9:30PM is 750 minutes after 9:00AM.
sarah_available_from = 210
sarah_available_until = 750

# Constraints:
# 1. You arrive at Sunset District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 30 minutes to travel from Sunset District to Union Square.
arrival_at_union = d + sunset_to_union

# 3. The meeting with Sarah cannot start until you have arrived at Union Square,
#    and she is available starting from 12:30PM.
opt.add(m_start >= arrival_at_union)
opt.add(m_start >= sarah_available_from)

# 4. Sarah is available until 9:30PM.
opt.add(m_end <= sarah_available_until)

# 5. You'd like to meet Sarah for a minimum of 15 minutes.
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
    
    # Helper function to convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Sunset District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Union Square at: {to_time(d_val + sunset_to_union)} (travel time = {sunset_to_union} minutes)")
    print(f"  Meeting with Sarah starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Sarah ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")