from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# We measure time in minutes after 9:00AM.
# Variables:
#   d: departure time from Chinatown (in minutes after 9:00AM)
#   m_start: meeting start time at Marina District (in minutes after 9:00AM)
#   m_end: meeting end time at Marina District (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel times (in minutes)
# Chinatown -> Marina District takes 12 minutes.
chinatown_to_marina = 12

# Stephanie's availability at Marina District:
#   She is available from 8:00AM to 3:00PM.
# Measuring relative to 9:00AM, 8:00AM = -60 minutes and 3:00PM = 360 minutes.
stephanie_available_from = -60
stephanie_available_until = 360

# Constraints:

# 1. You arrive at Chinatown at 9:00AM, so you can only leave at or after 9:00AM.
opt.add(d >= 0)

# 2. After departing Chinatown, you take 12 minutes to reach Marina District.
arrival_at_marina = d + chinatown_to_marina

# 3. You cannot start the meeting until you have arrived at Marina District.
#    Also, Stephanie is present from 8:00AM onward (i.e. from -60 minutes relative to 9:00AM),
#    so the effective lower bound is your arrival time.
opt.add(m_start >= arrival_at_marina)

# 4. Stephanie is only available until 3:00PM, i.e., 360 minutes after 9:00AM.
opt.add(m_end <= stephanie_available_until)

# 5. You'd like to meet Stephanie for at least 105 minutes.
opt.add(m_end - m_start >= 105)

# We want to maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve and output the optimal scheduling solution.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()

    # A helper function to convert minutes after 9:00AM to a formatted time (HH:MM).
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Chinatown at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Marina District at: {to_time(d_val + chinatown_to_marina)} (travel time = {chinatown_to_marina} minutes)")
    print(f"  Meeting with Stephanie starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Stephanie ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")