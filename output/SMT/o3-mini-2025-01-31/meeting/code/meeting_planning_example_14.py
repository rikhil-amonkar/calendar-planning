from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# Define time variables in minutes after 9:00AM.
# d: departure time from Nob Hill
# m_start: meeting start time at Marina District
# m_end: meeting end time at Marina District
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Nob Hill to Marina District is 11 minutes.
nobhill_to_marina = 11

# Mary's availability at Marina District:
# 8:00PM is 11 hours after 9:00AM => 660 minutes.
# 10:00PM is 13 hours after 9:00AM => 780 minutes.
mary_start = 660
mary_end = 780

# Constraints:

# 1. You arrive at Nob Hill at 9:00AM; you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Travel from Nob Hill to Marina District takes 11 minutes.
arrival_at_marina = d + nobhill_to_marina

# 3. You cannot start the meeting until you have arrived at Marina District and Mary is available.
opt.add(m_start >= arrival_at_marina)
opt.add(m_start >= mary_start)

# 4. Mary is available only until 10:00PM.
opt.add(m_end <= mary_end)

# 5. You'd like to meet Mary for at least 120 minutes.
opt.add(m_end - m_start >= 120)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()

    # Helper function to convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Nob Hill at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Marina District at: {to_time(d_val + nobhill_to_marina)} (travel time = {nobhill_to_marina} minutes)")
    print(f"  Meeting with Mary starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Mary ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")