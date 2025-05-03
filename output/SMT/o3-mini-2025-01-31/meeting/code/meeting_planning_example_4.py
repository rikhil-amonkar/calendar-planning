from z3 import Optimize, Int, sat

# Create the optimizer instance
opt = Optimize()

# Time is measured in minutes after 9:00AM.
# d: departure time from Presidio (in minutes after 9:00AM)
# m_start: meeting start time at Marina District (in minutes after 9:00AM)
# m_end: meeting end time at Marina District (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time in minutes:
presidio_to_marina = 10  # minutes to travel from Presidio to Marina District

# Jessica is at Marina District from 9:15AM to 5:45PM.
# To measure these times in minutes after 9:00AM:
# 9:15AM is 15 minutes after 9:00AM.
# 5:45PM is 8 hours 45 minutes after 9:00AM -> 8 * 60 + 45 = 525 minutes.
jessica_arrival = 15
jessica_departure = 525

# Constraints:
# 1. You arrive at Presidio at 9:00AM, so you cannot leave before 9:00AM.
opt.add(d >= 0)

# 2. After departing Presidio, travel to Marina District takes 10 minutes.
arrival_at_marina = d + presidio_to_marina

# 3. You cannot start the meeting until you have arrived at Marina District and until Jessica is available.
opt.add(m_start >= arrival_at_marina)
opt.add(m_start >= jessica_arrival)

# 4. Jessica is available only until 5:45PM.
opt.add(m_end <= jessica_departure)

# 5. You want to meet Jessica for at least 60 minutes.
opt.add(m_end - m_start >= 60)

# Objective: maximize the meeting duration, which is m_end - m_start.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the optimization problem and print the schedule
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function to convert minutes after 9:00AM to a time string (HH:MM)
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Presidio at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Marina District at: {to_time(d_val + presidio_to_marina)} (travel time = {presidio_to_marina} minutes)")
    print(f"  Meeting with Jessica starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Jessica ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")