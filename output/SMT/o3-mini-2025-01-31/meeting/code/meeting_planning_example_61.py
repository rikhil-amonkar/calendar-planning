from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Golden Gate Park (in minutes after 9:00AM)
#   m_start: meeting start time at Presidio (in minutes after 9:00AM)
#   m_end: meeting end time at Presidio (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Golden Gate Park to Presidio is 11 minutes.
ggp_to_presidio = 11

# Stephanie's availability at Presidio:
# From 7:15PM to 10:00PM.
# Convert times to minutes after 9:00AM:
# 7:15PM is 10 hours 15 minutes after 9:00AM => 10 * 60 + 15 = 615 minutes.
# 10:00PM is 13 hours after 9:00AM => 13 * 60 = 780 minutes.
stephanie_avail_from = 615
stephanie_avail_until = 780

# Constraints:
# 1. You arrive at Golden Gate Park at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival time at Presidio is your departure time plus the travel time.
arrival_at_presidio = d + ggp_to_presidio

# 3. The meeting with Stephanie can begin only after you have arrived at Presidio,
#    and not before Stephanie is available.
opt.add(m_start >= arrival_at_presidio)
opt.add(m_start >= stephanie_avail_from)

# 4. The meeting must end by the time Stephanie's availability ends.
opt.add(m_end <= stephanie_avail_until)

# 5. You'd like to meet Stephanie for a minimum of 90 minutes.
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
    
    # Helper function: convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    print("Optimal Schedule:")
    print(f"  Depart Golden Gate Park at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Presidio at: {to_time(d_val + ggp_to_presidio)} (travel time = {ggp_to_presidio} minutes)")
    print(f"  Meeting with Stephanie starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Stephanie ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")