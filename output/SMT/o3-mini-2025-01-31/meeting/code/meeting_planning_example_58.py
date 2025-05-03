from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from The Castro (in minutes after 9:00AM)
#   m_start: meeting start time at Financial District (in minutes after 9:00AM)
#   m_end: meeting end time at Financial District (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from The Castro to Financial District is 20 minutes.
castro_to_fd = 20

# Nancy's availability at Financial District:
# From 9:15AM to 4:45PM.
# 9:15AM is 15 minutes after 9:00AM.
nancy_avail_from = 15
# 4:45PM is 7 hours and 45 minutes after 9:00AM, i.e., 465 minutes.
nancy_avail_until = 465

# Constraints:

# 1. You arrive at The Castro at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival time at Financial District is your departure time plus the travel time.
arrival_at_fd = d + castro_to_fd

# 3. The meeting with Nancy can only start after you have arrived at Financial District
#    and not before Nancy is available.
opt.add(m_start >= arrival_at_fd)
opt.add(m_start >= nancy_avail_from)

# 4. The meeting must end by the time Nancy's availability ends.
opt.add(m_end <= nancy_avail_until)

# 5. You'd like to meet Nancy for a minimum of 30 minutes.
opt.add(m_end - m_start >= 30)

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
    print(f"  Depart The Castro at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Financial District at: {to_time(d_val + castro_to_fd)} (travel time = {castro_to_fd} minutes)")
    print(f"  Meeting with Nancy starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Nancy ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")