from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Richmond District (in minutes after 9:00AM)
#   m_start: meeting start time at Bayview (in minutes after 9:00AM)
#   m_end: meeting end time at Bayview (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Richmond District to Bayview is 26 minutes.
rd_to_bayview = 26

# Sarah's availability at Bayview:
# 2:15PM is 315 minutes after 9:00AM.
# 5:30PM is 510 minutes after 9:00AM.
sarah_avail_from = 315
sarah_avail_until = 510

# Constraints:

# 1. You arrive at Richmond District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 26 minutes to travel from Richmond District to Bayview.
arrival_at_bayview = d + rd_to_bayview

# 3. The meeting with Sarah cannot start until you've arrived at Bayview 
#    and not before Sarah's availability begins.
opt.add(m_start >= arrival_at_bayview)
opt.add(m_start >= sarah_avail_from)

# 4. The meeting must end by the time Sarah's availability ends.
opt.add(m_end <= sarah_avail_until)

# 5. You'd like to meet Sarah for a minimum of 45 minutes.
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
    
    # Helper function: convert minutes after 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Richmond District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Bayview at: {to_time(d_val + rd_to_bayview)} (travel time = {rd_to_bayview} minutes)")
    print(f"  Meeting with Sarah starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Sarah ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")