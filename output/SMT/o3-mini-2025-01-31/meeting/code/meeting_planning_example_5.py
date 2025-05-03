from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# Time is in minutes after 9:00AM.
# d: departure time from Nob Hill (minutes after 9:00AM)
# m_start: meeting start time at The Castro (minutes after 9:00AM)
# m_end: meeting end time at The Castro (minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel times in minutes:
nobhill_to_castro = 17  # from Nob Hill to The Castro

# William is at The Castro from 12:15PM to 10:00PM.
# Convert times relative to 9:00AM:
# 12:15PM is 3 hours 15 minutes after 9:00AM = 195 minutes.
# 10:00PM is 13 hours after 9:00AM = 780 minutes.
william_arrival = 195
william_departure = 780

# Constraints:
# 1. You arrive at Nob Hill at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Travel from Nob Hill to The Castro takes 17 minutes.
arrival_at_castro = d + nobhill_to_castro

# 3. You cannot start meeting until you have arrived at The Castro and until William is available.
opt.add(m_start >= arrival_at_castro)
opt.add(m_start >= william_arrival)

# 4. William is available until 10:00PM.
opt.add(m_end <= william_departure)

# 5. You'd like to meet William for at least 75 minutes.
opt.add(m_end - m_start >= 75)

# Our goal is to maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve and display the solution
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()

    # Helper function to convert minutes after 9:00AM to actual time in HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9  # 9:00AM expressed in minutes from midnight plus offset.
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    print("Optimal Schedule:")
    print(f"  Depart Nob Hill at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at The Castro at: {to_time(d_val + nobhill_to_castro)} (travel time = {nobhill_to_castro} minutes)")
    print(f"  Meeting with William starts at: {to_time(m_start_val)}")
    print(f"  Meeting with William ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")