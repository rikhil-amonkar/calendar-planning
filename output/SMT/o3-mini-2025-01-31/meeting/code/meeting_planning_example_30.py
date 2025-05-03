from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Richmond District (in minutes after 9:00AM)
#   m_start: meeting start time at North Beach (in minutes after 9:00AM)
#   m_end: meeting end time at North Beach (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Richmond District to North Beach is 17 minutes.
richmond_to_northbeach = 17

# Stephanie's availability at North Beach:
# Available from 9:30AM to 4:15PM.
# 9:30AM is 30 minutes after 9:00AM.
# 4:15PM is 7 hours 15 minutes after 9:00AM, i.e., 435 minutes.
stephanie_available_from = 30
stephanie_available_until = 435

# Constraints:

# 1. You arrive at Richmond District at 9:00AM; thus, you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Traveling from Richmond District to North Beach takes 17 minutes.
arrival_at_northbeach = d + richmond_to_northbeach

# 3. The meeting with Stephanie cannot start until you have arrived at North Beach and 
#    not before Stephanie's available starting time.
opt.add(m_start >= arrival_at_northbeach)
opt.add(m_start >= stephanie_available_from)

# 4. Stephanie is available until 4:15PM.
opt.add(m_end <= stephanie_available_until)

# 5. You'd like to meet Stephanie for a minimum of 120 minutes.
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
    
    # Helper function to convert minutes after 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Richmond District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at North Beach at: {to_time(d_val + richmond_to_northbeach)} (travel time = {richmond_to_northbeach} minutes)")
    print(f"  Meeting with Stephanie starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Stephanie ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")