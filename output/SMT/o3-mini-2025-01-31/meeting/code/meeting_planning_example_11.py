from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# Time is measured in minutes after 9:00AM.
# Variables:
# d: departure time from Nob Hill (minutes after 9:00AM)
# m_start: meeting start time at Sunset District (minutes after 9:00AM)
# m_end: meeting end time at Sunset District (minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time:
nobhill_to_sunset = 25  # minutes from Nob Hill to Sunset District

# Carol's availability at Sunset District:
# 2:00PM is 5 hours after 9:00AM, i.e. 300 minutes
# 8:30PM is 11.5 hours after 9:00AM, i.e. 690 minutes
carol_arrival = 300
carol_departure = 690

# Constraints:
# 1. You arrive at Nob Hill at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Travel from Nob Hill to Sunset District takes 25 minutes.
arrival_at_sunset = d + nobhill_to_sunset

# 3. You cannot start the meeting until you have reached Sunset District and until Carol is available.
opt.add(m_start >= arrival_at_sunset)
opt.add(m_start >= carol_arrival)

# 4. Carol is available only until 8:30PM.
opt.add(m_end <= carol_departure)

# 5. You want to meet Carol for at least 75 minutes.
opt.add(m_end - m_start >= 75)

# Objective: maximize the meeting duration.
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
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Nob Hill at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Sunset District at: {to_time(d_val + nobhill_to_sunset)} (travel time = {nobhill_to_sunset} minutes)")
    print(f"  Meeting with Carol starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Carol ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")