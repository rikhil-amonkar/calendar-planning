from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are in minutes after 9:00AM.
# Variables:
#   d       : departure time from Alamo Square (in minutes after 9:00AM)
#   m_start : meeting start time at Haight-Ashbury (in minutes after 9:00AM)
#   m_end   : meeting end time at Haight-Ashbury (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Alamo Square to Haight-Ashbury is 5 minutes.
alamo_to_ha = 5

# Thomas's availability at Haight-Ashbury:
# Thomas is available from 11:00AM to 1:00PM.
# Relative to 9:00AM, 11:00AM is 120 minutes and 1:00PM is 240 minutes.
thomas_avail_from = 120
thomas_avail_until = 240

# CONSTRAINTS:

# 1. You arrive at Alamo Square at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival time at Haight-Ashbury is your departure time plus travel time.
arrival_at_ha = d + alamo_to_ha

# 3. The meeting with Thomas cannot start before you arrive at Haight-Ashbury,
#    and it cannot start before Thomas is available.
opt.add(m_start >= arrival_at_ha)
opt.add(m_start >= thomas_avail_from)

# 4. The meeting must end no later than Thomas's availability.
opt.add(m_end <= thomas_avail_until)

# 5. You'd like to meet Thomas for at least 30 minutes.
opt.add(m_end - m_start >= 30)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()

    # Helper function: convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Alamo Square at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Haight-Ashbury at: {to_time(d_val + alamo_to_ha)} (travel time = {alamo_to_ha} minutes)")
    print(f"  Meeting with Thomas starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Thomas ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")