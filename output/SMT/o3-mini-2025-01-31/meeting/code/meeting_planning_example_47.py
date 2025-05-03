from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Richmond District (in minutes after 9:00AM)
#   m_start: meeting start time at Nob Hill (in minutes after 9:00AM)
#   m_end: meeting end time at Nob Hill (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Richmond District to Nob Hill is 17 minutes.
richmond_to_nobhill = 17

# Paul's availability at Nob Hill:
# 9:30AM is 30 minutes after 9:00AM and 11:15AM is 135 minutes after 9:00AM.
paul_avail_from = 30
paul_avail_until = 135

# Constraints:

# 1. You arrive at Richmond District at 9:00AM. So you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 17 minutes to travel from Richmond District to Nob Hill.
arrival_at_nobhill = d + richmond_to_nobhill

# 3. The meeting with Paul cannot start until you have arrived at Nob Hill,
#    and not before Paul's availability begins.
opt.add(m_start >= arrival_at_nobhill)
opt.add(m_start >= paul_avail_from)

# 4. The meeting must end by the end of Paul's availability.
opt.add(m_end <= paul_avail_until)

# 5. You'd like to meet Paul for a minimum of 15 minutes.
opt.add(m_end - m_start >= 15)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the problem.
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
    print(f"  Depart Richmond District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Nob Hill at: {to_time(d_val + richmond_to_nobhill)} (travel time = {richmond_to_nobhill} minutes)")
    print(f"  Meeting with Paul starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Paul ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")