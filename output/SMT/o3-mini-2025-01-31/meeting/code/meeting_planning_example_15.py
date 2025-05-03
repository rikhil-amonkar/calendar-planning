from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# Define variables (all times in minutes after 9:00AM):
# d: departure time from Russian Hill
# m_start: meeting start time at Golden Gate Park
# m_end: meeting end time at Golden Gate Park
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Russian Hill to Golden Gate Park is 21 minutes.
russianhill_to_ggp = 21

# John's availability at Golden Gate Park:
# 1:00PM is 240 minutes after 9:00AM.
# 6:15PM is 555 minutes after 9:00AM.
john_start = 240
john_end = 555

# Constraints:

# 1. You arrive at Russian Hill at 9:00AM, so you cannot leave before 9:00AM.
opt.add(d >= 0)

# 2. Travel from Russian Hill to Golden Gate Park takes 21 minutes.
arrival_at_ggp = d + russianhill_to_ggp

# 3. You cannot start the meeting until you have arrived at Golden Gate Park and until John is available.
opt.add(m_start >= arrival_at_ggp)
opt.add(m_start >= john_start)

# 4. John is available only until 6:15PM.
opt.add(m_end <= john_end)

# 5. You'd like to meet John for at least 90 minutes.
opt.add(m_end - m_start >= 90)

# Objective: Maximize the meeting duration (m_end - m_start).
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve and display the optimal schedule.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()

    # Helper function to convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9*60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    print("Optimal Schedule:")
    print(f"  Depart Russian Hill at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Golden Gate Park at: {to_time(d_val + russianhill_to_ggp)} (travel time = {russianhill_to_ggp} minutes)")
    print(f"  Meeting with John starts at: {to_time(m_start_val)}")
    print(f"  Meeting with John ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")