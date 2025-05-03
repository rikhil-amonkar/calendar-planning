from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
# d: departure time from North Beach (in minutes after 9:00 AM)
# m_start: meeting start time at Alamo Square (in minutes after 9:00 AM)
# m_end: meeting end time at Alamo Square (in minutes after 9:00 AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from North Beach to Alamo Square is 16 minutes.
nb_to_as = 16

# Emily's availability at Alamo Square:
# Available from 7:30PM to 9:00PM.
# 7:30 PM is 10.5 hours after 9:00AM, i.e., 630 minutes.
# 9:00 PM is 12 hours after 9:00AM, i.e., 720 minutes.
emily_avail_from = 630
emily_avail_until = 720

# Constraints:
# 1. You arrive at North Beach at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. After departing, you'll travel and arrive at Alamo Square after 16 minutes.
arrival_at_as = d + nb_to_as

# 3. The meeting can only start after you have arrived at Alamo Square,
#    and not before Emily is available.
opt.add(m_start >= arrival_at_as)
opt.add(m_start >= emily_avail_from)

# 4. The meeting must end by Emily's availability end time.
opt.add(m_end <= emily_avail_until)

# 5. You'd like to meet Emily for a minimum of 15 minutes.
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
    
    # Helper function to convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total = 9*60 + minutes_after_9
        hours = total // 60
        minutes = total % 60
        return f"{hours:02d}:{minutes:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart North Beach at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Alamo Square at: {to_time(d_val + nb_to_as)} (travel time = {nb_to_as} minutes)")
    print(f"  Meeting with Emily starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Emily ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")