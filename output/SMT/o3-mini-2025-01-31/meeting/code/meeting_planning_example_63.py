from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Presidio (in minutes after 9:00AM)
#   m_start: meeting start time at Bayview (in minutes after 9:00AM)
#   m_end: meeting end time at Bayview (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Presidio to Bayview is 31 minutes.
presidio_to_bayview = 31

# Nancy's availability at Bayview:
# 7:15AM => 7:15AM is 1 hour 45 minutes before 9:00AM, i.e., -105 minutes after 9:00AM.
# 5:30PM => from 9:00AM to 5:30PM is 8.5 hours, i.e., 510 minutes.
nancy_avail_from = -105
nancy_avail_until = 510

# Constraints:

# 1. You arrive at Presidio at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival at Bayview is your departure time plus travel time.
arrival_at_bayview = d + presidio_to_bayview

# 3. The meeting with Nancy can start only after you have arrived at Bayview
#    and not before Nancy is available.
opt.add(m_start >= arrival_at_bayview)
opt.add(m_start >= nancy_avail_from)

# 4. The meeting must end by the time Nancy's availability ends.
opt.add(m_end <= nancy_avail_until)

# 5. You'd like to meet Nancy for at least 30 minutes.
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
    
    # Helper function: converts minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Presidio at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Bayview at: {to_time(d_val + presidio_to_bayview)} (travel time = {presidio_to_bayview} minutes)")
    print(f"  Meeting with Nancy starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Nancy ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")