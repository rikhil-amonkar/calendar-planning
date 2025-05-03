from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Bayview (in minutes after 9:00AM)
#   m_start: meeting start time at Financial District (in minutes after 9:00AM)
#   m_end: meeting end time at Financial District (in minutes after 9:00AM)
d  = Int('d')
m_start = Int('m_start')
m_end   = Int('m_end')

# Given travel distance from Bayview to Financial District is 19 minutes.
bayview_to_fd = 19

# Jeffrey's availability at Financial District:
# From 12:15PM to 2:00PM.
# 12:15PM is 195 minutes after 9:00AM and 2:00PM is 300 minutes after 9:00AM.
jeffrey_avail_from = 195
jeffrey_avail_until = 300

# Constraints:
# 1. You arrive at Bayview at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Travel time: arrival at Financial District equals d + 19 minutes.
arrival_at_fd = d + bayview_to_fd

# 3. The meeting with Jeffrey can only start when you have arrived at Financial District,
#    and not before Jeffrey's availability.
opt.add(m_start >= arrival_at_fd)
opt.add(m_start >= jeffrey_avail_from)

# 4. The meeting must end by Jeffrey's availability end time.
opt.add(m_end <= jeffrey_avail_until)

# 5. You'd like to meet Jeffrey for a minimum of 90 minutes.
opt.add(m_end - m_start >= 90)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function to format minutes after 9:00AM to HH:MM.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Bayview at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Financial District at: {to_time(d_val + bayview_to_fd)} (travel time = {bayview_to_fd} minutes)")
    print(f"  Meeting with Jeffrey starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Jeffrey ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")