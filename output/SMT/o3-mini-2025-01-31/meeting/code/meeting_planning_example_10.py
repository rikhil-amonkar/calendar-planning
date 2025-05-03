from z3 import Optimize, Int, sat

# Create the optimizer instance
opt = Optimize()

# We measure time in minutes after 9:00AM.
# Variables:
#   d: Departure time from Golden Gate Park (in minutes after 9:00AM)
#   m_start: Meeting start time at Marina District (in minutes after 9:00AM)
#   m_end: Meeting end time at Marina District (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time (in minutes):
ggp_to_marina = 16  # from Golden Gate Park to Marina District

# James' availability at Marina District:
# 10:15AM is 75 minutes after 9:00AM.
# 1:30PM is 270 minutes after 9:00AM.
james_start = 75
james_end = 270

# Constraints:

# 1. You arrive at Golden Gate Park at 9:00AM, so you can only leave at or after 9:00AM.
opt.add(d >= 0)

# 2. Travel time from Golden Gate Park to Marina District takes 16 minutes.
arrival_at_marina = d + ggp_to_marina

# 3. The meeting with James cannot start until you've arrived at Marina District and until James has arrived.
opt.add(m_start >= arrival_at_marina)
opt.add(m_start >= james_start)

# 4. James is available until 1:30PM.
opt.add(m_end <= james_end)

# 5. You'd like to meet James for a minimum of 15 minutes.
opt.add(m_end - m_start >= 15)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem
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
    print(f"  Depart Golden Gate Park at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Marina District at: {to_time(d_val + ggp_to_marina)} (travel time = {ggp_to_marina} minutes)")
    print(f"  Meeting with James starts at: {to_time(m_start_val)}")
    print(f"  Meeting with James ends at: {to_time(m_end_val)}")
    print(f"  Meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")