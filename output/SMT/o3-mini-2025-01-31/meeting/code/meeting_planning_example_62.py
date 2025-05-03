from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Presidio (in minutes after 9:00AM)
#   m_start: meeting start time at Russian Hill (in minutes after 9:00AM)
#   m_end: meeting end time at Russian Hill (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Presidio to Russian Hill is 14 minutes.
presidio_to_rh = 14

# Amanda's availability at Russian Hill:
# From 11:30AM to 9:15PM.
# 11:30AM => 2.5 hours after 9:00AM = 150 minutes.
# 9:15PM  => 12 hours 15 minutes after 9:00AM = 735 minutes.
amanda_avail_from = 150
amanda_avail_until = 735

# Constraints:

# 1. You arrive at Presidio at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart Presidio at time d, you arrive at Russian Hill at:
arrival_at_rh = d + presidio_to_rh

# 3. The meeting with Amanda can start only after you have arrived at Russian Hill,
#    and not before Amanda is available.
opt.add(m_start >= arrival_at_rh)
opt.add(m_start >= amanda_avail_from)

# 4. The meeting must end by the end of Amanda's availability.
opt.add(m_end <= amanda_avail_until)

# 5. You'd like to meet Amanda for a minimum of 15 minutes.
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

    # Helper function to convert minutes after 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9*60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    print("Optimal Schedule:")
    print(f"  Depart Presidio at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Russian Hill at: {to_time(d_val + presidio_to_rh)} (travel time = {presidio_to_rh} minutes)")
    print(f"  Meeting with Amanda starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Amanda ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")