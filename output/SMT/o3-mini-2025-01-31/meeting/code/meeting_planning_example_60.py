from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Union Square (in minutes after 9:00AM)
#   m_start: meeting start time at Chinatown (in minutes after 9:00AM)
#   m_end: meeting end time at Chinatown (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Union Square to Chinatown is 7 minutes.
us_to_chinatown = 7

# Carol's availability at Chinatown:
# 6:30PM is 570 minutes after 9:00AM.
# 8:00PM is 660 minutes after 9:00AM.
carol_avail_from = 570
carol_avail_until = 660

# Constraints:

# 1. You arrive at Union Square at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart from Union Square at time d, you arrive at Chinatown at:
arrival_at_chinatown = d + us_to_chinatown

# 3. The meeting with Carol can only start after you've arrived at Chinatown,
#    and not before Carol is available.
opt.add(m_start >= arrival_at_chinatown)
opt.add(m_start >= carol_avail_from)

# 4. The meeting must end by the time Carol's availability ends.
opt.add(m_end <= carol_avail_until)

# 5. You'd like to meet Carol for a minimum of 45 minutes.
opt.add(m_end - m_start >= 45)

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
    print(f"  Depart Union Square at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Chinatown at: {to_time(d_val + us_to_chinatown)} (travel time = {us_to_chinatown} minutes)")
    print(f"  Meeting with Carol starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Carol ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")