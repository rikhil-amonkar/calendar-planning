from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes relative to 9:00AM.
# Variables:
#   d: departure time from Chinatown (in minutes after 9:00AM)
#   m_start: meeting start time at Union Square (in minutes after 9:00AM)
#   m_end: meeting end time at Union Square (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Chinatown to Union Square is 7 minutes.
chinatown_to_us = 7

# Mark's availability at Union Square:
# Mark is there from 8:00AM to 12:45PM.
# Relative to 9:00AM, 8:00AM is -60 minutes and 12:45PM is 225 minutes.
mark_avail_from = -60
mark_avail_until = 225

# Constraints:

# 1. You arrive at Chinatown at 9:00AM, so you can't depart before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival time at Union Square is d + travel time.
arrival_at_us = d + chinatown_to_us

# 3. The meeting with Mark can only start after you have arrived at Union Square
#    and not before Mark is available.
opt.add(m_start >= arrival_at_us)
opt.add(m_start >= mark_avail_from)

# 4. The meeting must end by the time Mark's availability ends.
opt.add(m_end <= mark_avail_until)

# 5. You'd like to meet Mark for a minimum of 90 minutes.
opt.add(m_end - m_start >= 90)

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
    print(f"  Depart Chinatown at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Union Square at: {to_time(d_val + chinatown_to_us)} (travel time = {chinatown_to_us} minutes)")
    print(f"  Meeting with Mark starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Mark ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")