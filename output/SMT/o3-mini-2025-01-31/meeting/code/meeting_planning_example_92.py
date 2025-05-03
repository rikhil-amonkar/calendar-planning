from z3 import Optimize, Int, sat

# Create the optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from Financial District (in minutes after 9:00AM)
#   m_start : meeting start time at The Castro (in minutes after 9:00AM)
#   m_end   : meeting end time at The Castro (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Financial District to The Castro is 23 minutes.
fd_to_castro = 23

# Carol's availability at The Castro:
# 2:00PM is 5 hours after 9:00AM -> 300 minutes.
# 5:45PM is 8 hours and 45 minutes after 9:00AM -> 525 minutes.
carol_avail_from = 300
carol_avail_until = 525

# CONSTRAINTS:

# 1. You arrive at Financial District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart Financial District at time 'd', you arrive at The Castro at:
arrival_at_castro = d + fd_to_castro

# 3. The meeting with Carol cannot start before you arrive at The Castro,
#    and it cannot start before Carol is available.
opt.add(m_start >= arrival_at_castro)
opt.add(m_start >= carol_avail_from)

# 4. The meeting must end by the time Carol's availability ends.
opt.add(m_end <= carol_avail_until)

# 5. You’d like to meet Carol for at least 45 minutes.
opt.add(m_end - m_start >= 45)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function to convert minutes after 9:00AM to a HH:MM time format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Financial District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at The Castro at: {to_time(d_val + fd_to_castro)} (travel time = {fd_to_castro} minutes)")
    print(f"  Meeting with Carol starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Carol ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")