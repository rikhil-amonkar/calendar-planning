from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# Time is measured in minutes after 9:00AM.
# d: departure time from Bayview (in minutes after 9:00AM)
# m_start: the time when the meeting with Barbara starts at Golden Gate Park (in minutes after 9:00AM)
# m_end: the time when the meeting with Barbara ends at Golden Gate Park (in minutes after 9:00AM)

d = Int('d')         # departure time from Bayview
m_start = Int('m_start')   # meeting start time at Golden Gate Park with Barbara
m_end = Int('m_end')       # meeting end time at Golden Gate Park with Barbara

# Given travel time in minutes:
bayview_to_ggp = 22   # minutes to travel from Bayview to Golden Gate Park

# Barbara is available at Golden Gate Park from 8:00AM to 11:30AM.
# Since we measure time relative to 9:00AM:
# 8:00AM => -60 minutes (i.e. one hour before 9:00AM)
# 11:30AM => 150 minutes (i.e. 2.5 hours after 9:00AM)
barbara_arrival = -60   # in minutes after 9:00AM
barbara_departure = 150

# Constraints:
# 1. You arrive at Bayview at 9:00AM, so you can only leave at or after 9:00AM.
opt.add(d >= 0)

# 2. After departing Bayview, travel to Golden Gate Park takes 22 minutes.
arrival_at_ggp = d + bayview_to_ggp

# 3. You can't start a meeting until you've arrived at Golden Gate Park.
# Additionally, Barbara is available starting at 8:00AM; since 8:00AM is before 9:00AM,
# the effective lower bound for starting the meeting is your arrival time at Golden Gate Park.
opt.add(m_start >= arrival_at_ggp)
opt.add(m_start >= barbara_arrival)  # Redundant in this case, as arrival_at_ggp will be >= 22

# 4. Barbara is available only until 11:30AM (which is 150 minutes after 9:00AM)
opt.add(m_end <= barbara_departure)

# 5. You would like to meet Barbara for at least 90 minutes.
opt.add(m_end - m_start >= 90)

# Our goal is to maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Check and display the optimal schedule
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Function to convert minutes after 9:00AM into HH:MM format
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Bayview at {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Golden Gate Park at {to_time(d_val + bayview_to_ggp)} (travel time = {bayview_to_ggp} minutes)")
    print(f"  Meeting with Barbara starts at {to_time(m_start_val)}")
    print(f"  Meeting with Barbara ends at {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")