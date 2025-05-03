from z3 import Optimize, Int, sat

# Create the optimizer instance
opt = Optimize()

# All times are in minutes after 9:00AM.
# Variables:
#   d       : departure time from Mission District (in minutes after 9:00AM)
#   m_start : start time of meeting with Joshua at Haight-Ashbury (in minutes after 9:00AM)
#   m_end   : end time of meeting with Joshua at Haight-Ashbury (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Mission District to Haight-Ashbury is 12 minutes.
md_to_ha = 12

# Joshua's availability at Haight-Ashbury:
# 11:30AM is 150 minutes after 9:00AM.
# 10:00PM is 780 minutes after 9:00AM.
joshua_avail_from = 150
joshua_avail_until = 780

# CONSTRAINTS:

# 1. You arrive at Mission District at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival time at Haight-Ashbury is the departure time plus travel time.
arrival_at_ha = d + md_to_ha

# 3. The meeting with Joshua cannot start before you arrive at Haight-Ashbury,
#    and it cannot start before his availability begins.
opt.add(m_start >= arrival_at_ha)
opt.add(m_start >= joshua_avail_from)

# 4. The meeting must end by the time Joshua's availability ends.
opt.add(m_end <= joshua_avail_until)

# 5. You'd like to meet Joshua for at least 75 minutes.
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
    
    # Helper function to convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Mission District at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Haight-Ashbury at: {to_time(d_val + md_to_ha)} (travel time = {md_to_ha} minutes)")
    print(f"  Meeting with Joshua starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Joshua ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")