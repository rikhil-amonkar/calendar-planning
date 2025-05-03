from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes relative to 9:00AM.
# Variables:
#   d: departure time from Bayview (in minutes after 9:00AM)
#   m_start: meeting start time at Haight-Ashbury (in minutes after 9:00AM)
#   m_end: meeting end time at Haight-Ashbury (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Bayview to Haight-Ashbury is 19 minutes.
bayview_to_haight = 19

# Richard's availability at Haight-Ashbury runs from 7:00AM to 3:45PM.
# We set our time zero at 9:00AM, so:
# 7:00AM = 9:00AM - 120 minutes --> availability start = -120
# 3:45PM = 9:00AM + 6 hours 45 minutes = 405 minutes --> availability end = 405
richard_avail_from = -120
richard_avail_until = 405

# Constraint: You arrive at Bayview at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# When you depart Bayview at time d, you arrive at Haight-Ashbury at:
arrival_at_haight = d + bayview_to_haight

# The meeting with Richard must start after you have arrived at Haight-Ashbury,
# and it cannot start before Richard is available.
opt.add(m_start >= arrival_at_haight)
opt.add(m_start >= richard_avail_from)

# The meeting must finish by the time Richard's availability ends.
opt.add(m_end <= richard_avail_until)

# You want to meet Richard for at least 105 minutes.
opt.add(m_end - m_start >= 105)

# Objective: maximize the meeting duration (for example,
# to optimize the overall time spent with friends).
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve using the Z3 optimizer.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function to convert minutes relative to 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Bayview at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Haight-Ashbury at: {to_time(d_val + bayview_to_haight)} (travel time = {bayview_to_haight} minutes)")
    print(f"  Meeting with Richard starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Richard ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")