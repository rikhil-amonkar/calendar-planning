from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from The Castro (in minutes after 9:00AM)
#   m_start: meeting start time at Sunset District (in minutes after 9:00AM)
#   m_end: meeting end time at Sunset District (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from The Castro to Sunset District is 17 minutes.
castro_to_sunset = 17

# Deborah's availability at Sunset District:
# 2:15PM is 5 hours and 15 minutes after 9:00AM, i.e., 315 minutes.
# 8:00PM is 11 hours after 9:00AM, i.e., 660 minutes.
deborah_avail_from = 315
deborah_avail_until = 660

# Constraints:

# 1. You arrive at The Castro at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Travel from The Castro to Sunset District takes 17 minutes.
arrival_at_sunset = d + castro_to_sunset

# 3. The meeting with Deborah cannot start until both you have arrived at Sunset District 
#    and Deborah is available.
opt.add(m_start >= arrival_at_sunset)
opt.add(m_start >= deborah_avail_from)

# 4. The meeting must end by the time Deborah is available until.
opt.add(m_end <= deborah_avail_until)

# 5. You’d like to meet Deborah for a minimum of 75 minutes.
opt.add(m_end - m_start >= 75)

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
    print(f"  Depart The Castro at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Sunset District at: {to_time(d_val + castro_to_sunset)} (travel time = {castro_to_sunset} minutes)")
    print(f"  Meeting with Deborah starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Deborah ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")