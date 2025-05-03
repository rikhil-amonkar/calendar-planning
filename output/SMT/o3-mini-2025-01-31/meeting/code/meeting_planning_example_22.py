from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# Variables (all times in minutes after 9:00AM):
# d: departure time from Presidio
# m_start: meeting start time at Union Square
# m_end: meeting end time at Union Square
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Travel time from Presidio to Union Square is 22 minutes.
presidio_to_union = 22

# Andrew's availability at Union Square:
# 11:15AM is 11:15 - 9:00 = 2 hours 15 minutes = 135 minutes after 9:00AM.
# 5:15PM is 5:15PM which is 8 hours 15 minutes after 9:00AM = 495 minutes.
andrew_start = 135
andrew_end = 495

# Constraints:
# 1. You arrive at Presidio at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 22 minutes to travel from Presidio to Union Square.
arrival_at_union = d + presidio_to_union

# 3. The meeting with Andrew cannot start until you have arrived at Union Square,
#    and until Andrew is available.
opt.add(m_start >= arrival_at_union)
opt.add(m_start >= andrew_start)

# 4. Andrew is available until 5:15PM.
opt.add(m_end <= andrew_end)

# 5. You'd like to meet Andrew for at least 105 minutes.
opt.add(m_end - m_start >= 105)

# Objective: Maximize the meeting duration.
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
    print(f"  Depart Presidio at: {to_time(d_val)} (9:00AM + {d_val} mins)")
    print(f"  Arrive at Union Square at: {to_time(d_val + presidio_to_union)} (travel time = {presidio_to_union} mins)")
    print(f"  Meeting with Andrew starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Andrew ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")