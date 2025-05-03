from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# Time is measured in minutes after 9:00AM.
# Variables:
# d: departure time from Richmond District (in minutes after 9:00AM)
# m_start: meeting start time at North Beach (in minutes after 9:00AM)
# m_end: meeting end time at North Beach (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time (in minutes):
richmond_to_northbeach = 17  # travel time from Richmond District to North Beach

# John's availability at North Beach:
# 3:15PM corresponds to 6 hours 15 minutes after 9:00AM, which equals 375 minutes.
# 5:15PM corresponds to 8 hours 15 minutes after 9:00AM, which equals 495 minutes.
john_arrival = 375
john_departure = 495

# Constraints:

# 1. You arrive at Richmond District at 9:00AM, so you cannot leave before that time.
opt.add(d >= 0)

# 2. After departing from Richmond, you need 17 minutes to reach North Beach.
arrival_at_northbeach = d + richmond_to_northbeach

# 3. You cannot start the meeting until you have arrived at North Beach and until John is available.
opt.add(m_start >= arrival_at_northbeach)
opt.add(m_start >= john_arrival)

# 4. John is available until 5:15PM.
opt.add(m_end <= john_departure)

# 5. You'd like to meet John for at least 75 minutes.
opt.add(m_end - m_start >= 75)

# Objective: Maximize the meeting duration (m_end - m_start)
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Check and output the solution.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()

    # Function to convert minutes after 9:00AM to HH:MM format.
    def to_time(min_after_9):
        total_minutes = 9 * 60 + min_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    print("Optimal Schedule:")
    print(f"  Depart Richmond District at {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at North Beach at {to_time(d_val + richmond_to_northbeach)} (travel time = {richmond_to_northbeach} minutes)")
    print(f"  Meeting with John starts at {to_time(m_start_val)}")
    print(f"  Meeting with John ends at {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")