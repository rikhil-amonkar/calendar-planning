from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from Union Square (in minutes after 9:00AM)
#   m_start : meeting start time at The Castro (in minutes after 9:00AM)
#   m_end   : meeting end time at The Castro (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Union Square to The Castro is 19 minutes.
us_to_castro = 19

# Michelle's availability at The Castro:
# 6:00PM is 6 hours after 12:00PM? No, let's calculate relative to 9:00AM:
# 6:00PM is 9 hours after 9:00AM => 9*60 = 540 minutes.
# 8:00PM is 11 hours after 9:00AM => 11*60 = 660 minutes.
michelle_avail_from = 540
michelle_avail_until = 660

# CONSTRAINTS:

# 1. You arrive at Union Square at 9:00AM, so you cannot leave before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival time at The Castro is your departure time plus travel time.
arrival_at_castro = d + us_to_castro

# 3. The meeting with Michelle cannot start before you arrive at The Castro or before her availability begins.
opt.add(m_start >= arrival_at_castro)
opt.add(m_start >= michelle_avail_from)

# 4. The meeting must end by the end of Michelle's availability.
opt.add(m_end <= michelle_avail_until)

# 5. You'd like to meet Michelle for at least 105 minutes.
opt.add(m_end - m_start >= 105)

# Objective: maximize the total meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()

    # Helper function: Convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Union Square at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at The Castro at: {to_time(d_val + us_to_castro)} (travel time = {us_to_castro} minutes)")
    print(f"  Meeting with Michelle starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Michelle ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")