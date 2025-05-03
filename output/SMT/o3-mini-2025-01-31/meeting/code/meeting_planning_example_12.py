from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# Variables:
# d: departure time from North Beach (in minutes after 9:00AM)
# m_start: meeting start time at Alamo Square (in minutes after 9:00AM)
# m_end: meeting end time at Alamo Square (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel times (in minutes):
northbeach_to_alamo = 16

# Barbara's availability at Alamo Square:
# 6:00PM is 540 minutes after 9:00AM.
# 9:30PM is 750 minutes after 9:00AM.
barbara_arrival = 540
barbara_departure = 750

# Constraints:
# 1. You arrive at North Beach at 9:00AM, hence you can only depart at or after 9:00AM.
opt.add(d >= 0)

# 2. Traveling from North Beach to Alamo Square takes 16 minutes.
arrival_at_alamo = d + northbeach_to_alamo

# 3. You cannot start meeting until you have arrived at Alamo Square and Barbara is available.
opt.add(m_start >= arrival_at_alamo)
opt.add(m_start >= barbara_arrival)

# 4. Barbara is available only until 9:30PM.
opt.add(m_end <= barbara_departure)

# 5. You'd like to meet Barbara for at least 90 minutes.
opt.add(m_end - m_start >= 90)

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
    print(f"  Depart North Beach at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Alamo Square at: {to_time(d_val + northbeach_to_alamo)} (travel time = {northbeach_to_alamo} minutes)")
    print(f"  Meeting with Barbara starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Barbara ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")