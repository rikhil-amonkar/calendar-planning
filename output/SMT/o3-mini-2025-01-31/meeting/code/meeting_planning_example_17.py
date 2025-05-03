from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are in minutes after 9:00AM.
# d: departure time from Alamo Square
# m_start: meeting start time at Sunset District
# m_end: meeting end time at Sunset District
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time (in minutes)
alamo_to_sunset = 16

# Matthew's availability at Sunset District:
# 1:30PM is 270 minutes after 9:00AM.
# 2:30PM is 330 minutes after 9:00AM.
matthew_available_from = 270
matthew_available_until = 330

# Constraints:

# 1. You arrive at Alamo Square at 9:00AM and cannot depart before then.
opt.add(d >= 0)

# 2. It takes 16 minutes to travel from Alamo Square to Sunset District.
arrival_at_sunset = d + alamo_to_sunset

# 3. The meeting with Matthew cannot start until you have arrived at Sunset District
#    and until Matthew is available.
opt.add(m_start >= arrival_at_sunset)
opt.add(m_start >= matthew_available_from)

# 4. Matthew is available only until 2:30PM.
opt.add(m_end <= matthew_available_until)

# 5. You'd like to meet Matthew for at least 15 minutes.
opt.add(m_end - m_start >= 15)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()

    # Helper function to convert minutes after 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Alamo Square at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Sunset District at: {to_time(d_val + alamo_to_sunset)} (travel time = {alamo_to_sunset} minutes)")
    print(f"  Meeting with Matthew starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Matthew ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")