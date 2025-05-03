from z3 import Optimize, Int, sat

# Create the optimizer instance
opt = Optimize()

# Variables (minutes after 9:00AM):
# d: departure time from Presidio
# m_start: meeting start time at North Beach
# m_end: meeting end time at North Beach
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel times in minutes:
presidio_to_northbeach = 18

# Betty's availability at North Beach:
# 6:45PM: 9:00AM -> 6:45PM is 9 hours 45 minutes later = 585 minutes after 9:00AM.
# 10:00PM: 9:00AM -> 10:00PM is 13 hours after 9:00AM = 780 minutes.
betty_arrival = 585
betty_departure = 780

# Constraints:

# 1. You arrive at Presidio at 9:00AM so you cannot leave before that.
opt.add(d >= 0)

# 2. You travel from Presidio to North Beach; arriving time is d + travel time.
arrival_at_northbeach = d + presidio_to_northbeach

# 3. The meeting with Betty can only start after you've arrived at North Beach and after Betty has arrived.
opt.add(m_start >= arrival_at_northbeach)
opt.add(m_start >= betty_arrival)

# 4. Betty is available only until 10:00PM.
opt.add(m_end <= betty_departure)

# 5. You'd like to meet Betty for a minimum of 75 minutes.
opt.add(m_end - m_start >= 75)

# Objective: Maximize the meeting duration (m_end - m_start)
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
    print(f"  Depart Presidio at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at North Beach at: {to_time(d_val + presidio_to_northbeach)} (travel time = {presidio_to_northbeach} minutes)")
    print(f"  Meeting with Betty starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Betty ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")