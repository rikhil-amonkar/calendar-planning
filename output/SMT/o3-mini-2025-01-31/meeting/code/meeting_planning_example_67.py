from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are in minutes after 9:00AM.
# Variables:
#    d      : departure time from Golden Gate Park (in minutes after 9:00AM)
#    m_start: meeting start time at Financial District (in minutes after 9:00AM)
#    m_end  : meeting end time at Financial District (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Golden Gate Park to Financial District is 26 minutes.
ggp_to_fd = 26

# Kenneth's availability at Financial District:
# 8:00PM is 11 hours after 9:00AM: 11*60 = 660 minutes.
# 10:00PM is 13 hours after 9:00AM: 13*60 = 780 minutes.
kenneth_avail_from = 660
kenneth_avail_until = 780

# Constraints:

# 1. Since you are at Golden Gate Park at 9:00AM, you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival time at the Financial District is: d + travel time.
arrival_at_fd = d + ggp_to_fd

# 3. The meeting with Kenneth can only begin after you have arrived and after his availability begins.
opt.add(m_start >= arrival_at_fd)
opt.add(m_start >= kenneth_avail_from)

# 4. The meeting must end by the time Kenneth's availability ends.
opt.add(m_end <= kenneth_avail_until)

# 5. You'd like to meet Kenneth for at least 105 minutes.
opt.add(m_end - m_start >= 105)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function: converts minutes after 9:00AM to HH:MM.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Golden Gate Park at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Financial District at: {to_time(d_val + ggp_to_fd)} (travel time = {ggp_to_fd} minutes)")
    print(f"  Meeting with Kenneth starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Kenneth ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")