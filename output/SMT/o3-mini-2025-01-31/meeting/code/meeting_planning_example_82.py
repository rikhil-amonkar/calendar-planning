from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d       : departure time from Golden Gate Park (in minutes after 9:00AM)
#   m_start : meeting start time at Alamo Square (in minutes after 9:00AM)
#   m_end   : meeting end time at Alamo Square (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Golden Gate Park to Alamo Square is 10 minutes.
ggp_to_alamo = 10

# Ashley's availability at Alamo Square:
# 5:45PM is 525 minutes after 9:00AM.
# 9:30PM is 750 minutes after 9:00AM.
ashley_avail_from = 525
ashley_avail_until = 750

# CONSTRAINTS:

# 1. You arrive at Golden Gate Park at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. When you depart from Golden Gate Park at time d, you will arrive at Alamo Square at d + travel time.
arrival_at_alamo = d + ggp_to_alamo

# 3. The meeting with Ashley cannot start before you arrive at Alamo Square,
#    and not before Ashley is available.
opt.add(m_start >= arrival_at_alamo)
opt.add(m_start >= ashley_avail_from)

# 4. The meeting must end no later than Ashley's availability.
opt.add(m_end <= ashley_avail_until)

# 5. You'd like to meet Ashley for at least 75 minutes.
opt.add(m_end - m_start >= 75)

# Objective: Maximize the meeting duration.
opt.maximize(m_end - m_start)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper: Convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9*60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Golden Gate Park at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Alamo Square at: {to_time(d_val + ggp_to_alamo)} (travel time = {ggp_to_alamo} minutes)")
    print(f"  Meeting with Ashley starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Ashley ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")