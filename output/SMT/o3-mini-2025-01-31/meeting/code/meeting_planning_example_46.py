from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#  d: departure time from Haight-Ashbury (in minutes after 9:00AM)
#  m_start: meeting start time at North Beach (in minutes after 9:00AM)
#  m_end: meeting end time at North Beach (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Haight-Ashbury to North Beach is 19 minutes.
haight_to_nb = 19

# Robert's availability at North Beach:
# From 4:30PM to 9:30PM.
# 4:30PM is 7.5 hours after 9:00AM, i.e., 450 minutes after 9:00AM.
# 9:30PM is 12.5 hours after 9:00AM, i.e., 750 minutes after 9:00AM.
robert_avail_from = 450
robert_avail_until = 750

# Constraints:

# 1. You arrive at Haight-Ashbury at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Travel from Haight-Ashbury to North Beach takes 19 minutes.
arrival_at_nb = d + haight_to_nb

# 3. The meeting with Robert cannot start until you've arrived at North Beach and not before Robert is available.
opt.add(m_start >= arrival_at_nb)
opt.add(m_start >= robert_avail_from)

# 4. The meeting must end by the time Robert's availability ends.
opt.add(m_end <= robert_avail_until)

# 5. You'd like to meet Robert for a minimum of 90 minutes.
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
    print(f"  Depart Haight-Ashbury at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at North Beach at: {to_time(d_val + haight_to_nb)} (travel time = {haight_to_nb} minutes)")
    print(f"  Meeting with Robert starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Robert ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")