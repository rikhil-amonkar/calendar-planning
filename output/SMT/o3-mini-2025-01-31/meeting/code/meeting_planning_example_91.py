from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from Russian Hill (in minutes after 9:00AM)
#   m_start : meeting start time at Richmond District (in minutes after 9:00AM)
#   m_end   : meeting end time at Richmond District (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Russian Hill to Richmond District is 14 minutes.
rh_to_rd = 14

# Daniel's availability at Richmond District:
# 7:00PM is 600 minutes after 9:00AM (7:00PM = 9:00AM + 10 hours = 600 minutes),
# 8:15PM is 675 minutes after 9:00AM.
daniel_avail_from = 600
daniel_avail_until = 675

# CONSTRAINTS:

# 1. You arrive at Russian Hill at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart from Russian Hill at time d, you arrive at Richmond District at:
arrival_at_rd = d + rh_to_rd

# 3. The meeting with Daniel cannot start before you arrive at Richmond District,
#    and cannot start before Daniel's availability begins.
opt.add(m_start >= arrival_at_rd)
opt.add(m_start >= daniel_avail_from)

# 4. The meeting must finish no later than Daniel's availability ends.
opt.add(m_end <= daniel_avail_until)

# 5. You'd like to meet Daniel for at least 75 minutes.
opt.add(m_end - m_start >= 75)

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
    print(f"  Depart Russian Hill at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Richmond District at: {to_time(d_val + rh_to_rd)} (travel time = {rh_to_rd} minutes)")
    print(f"  Meeting with Daniel starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Daniel ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")