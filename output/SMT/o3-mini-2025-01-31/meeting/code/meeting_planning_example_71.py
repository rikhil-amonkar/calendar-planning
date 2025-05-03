from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Haight-Ashbury (in minutes after 9:00AM)
#   m_start: meeting start time at Bayview (in minutes after 9:00AM)
#   m_end: meeting end time at Bayview (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Haight-Ashbury to Bayview is 18 minutes.
ha_to_bayview = 18

# Paul's availability at Bayview:
# From 11:00AM to 4:30PM.
# Relative to 9:00AM, 11:00AM is 120 minutes and 4:30PM is 450 minutes.
paul_avail_from = 120
paul_avail_until = 450

# Constraints:

# 1. You arrive at Haight-Ashbury at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival time at Bayview is your departure time plus the travel time.
arrival_at_bayview = d + ha_to_bayview

# 3. The meeting with Paul can only start after you have arrived at Bayview,
#    and not before Paul's availability begins.
opt.add(m_start >= arrival_at_bayview)
opt.add(m_start >= paul_avail_from)

# 4. The meeting must end by the time Paul's availability ends.
opt.add(m_end <= paul_avail_until)

# 5. You'd like to meet Paul for at least 90 minutes.
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

    # Helper function to convert minutes after 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    print("Optimal Schedule:")
    print(f"  Depart Haight-Ashbury at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Bayview at: {to_time(d_val + ha_to_bayview)} (travel time = {ha_to_bayview} minutes)")
    print(f"  Meeting with Paul starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Paul ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")