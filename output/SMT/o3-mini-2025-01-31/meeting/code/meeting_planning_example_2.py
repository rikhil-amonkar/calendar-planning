from z3 import Optimize, Int, sat

# Create an optimizer instance
opt = Optimize()

# Time is measured in minutes after 9:00AM.
# d: departure time from Haight-Ashbury (in minutes after 9:00AM)
# m_start: actual meeting start time at Sunset District (in minutes after 9:00AM)
# m_end: actual meeting end time at Sunset District (in minutes after 9:00AM)

d = Int('d')         # departure time from Haight-Ashbury
m_start = Int('m_start')   # meeting start time with Jessica
m_end = Int('m_end')       # meeting end time with Jessica

# Given travel time in minutes:
haight_to_sunset = 15  # minutes from Haight-Ashbury -> Sunset District

# Jessica is available in the Sunset District from 3:15PM to 8:15PM.
# Convert these times to minutes after 9:00AM:
# 3:15PM is 6 hours 15 minutes after 9:00AM = 375 minutes.
# 8:15PM is 11 hours 15 minutes after 9:00AM = 675 minutes.
jessica_arrival = 375  
jessica_departure = 675 

# Constraints:
# 1. You arrive at Haight-Ashbury at 9:00AM so you can only depart at or after 9:00AM.
opt.add(d >= 0)

# 2. Travel from Haight-Ashbury to Sunset District takes 15 minutes.
arrival_at_sunset = d + haight_to_sunset

# 3. You cannot start meeting until you have arrived at Sunset District 
#    and Jessica is available.
opt.add(m_start >= arrival_at_sunset)
opt.add(m_start >= jessica_arrival)

# 4. Jessica is available only until 8:15PM.
opt.add(m_end <= jessica_departure)

# 5. You want to meet Jessica for at least 90 minutes.
opt.add(m_end - m_start >= 90)

# Our goal is to maximize the meeting duration.
meeting_duration = m_end - m_start
objective = opt.maximize(meeting_duration)

# Check and display the optimal schedule
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Function to convert minutes after 9:00AM to a proper time string (HH:MM)
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9  # convert 9:00AM to minutes since midnight, then add offset
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Haight-Ashbury at {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Sunset District at {to_time(d_val + haight_to_sunset)} (travel time = {haight_to_sunset} minutes)")
    print(f"  Meeting with Jessica starts at {to_time(m_start_val)}")
    print(f"  Meeting with Jessica ends at {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")