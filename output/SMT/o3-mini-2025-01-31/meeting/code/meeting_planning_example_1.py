from z3 import Optimize, Int, sat

# Create an optimizer
opt = Optimize()

# Time is measured in minutes after 9:00AM.
# d: departure time from Richmond District (in minutes after 9:00AM)
# m_start: actual meeting start time at Financial District (in minutes after 9:00AM)
# m_end: actual meeting end time at Financial District (in minutes after 9:00AM)

d = Int('d')         # departure time from Richmond District
m_start = Int('m_start')   # meeting start time with Betty
m_end = Int('m_end')       # meeting end time with Betty

# Given travel times in minutes:
richmond_to_financial = 22   # minutes from Richmond District -> Financial District

# Betty is available in the Financial District from 5:15PM to 9:45PM.
# In minutes after 9:00AM, these are:
betty_arrival = 495   # 5:15PM is 495 minutes after 9:00AM
betty_departure = 765 # 9:45PM is 765 minutes after 9:00AM

# Constraints:
# 1. You arrive at Richmond District at 9:00AM so you can only leave Richmond after time 0.
opt.add(d >= 0)

# 2. You travel from Richmond to Financial District: travel takes 22 minutes.
arrival_at_financial = d + richmond_to_financial

# 3. You can't start meeting Betty until you have arrived in Financial District and she is available.
opt.add(m_start >= arrival_at_financial)
opt.add(m_start >= betty_arrival)

# 4. Betty will be in the Financial District only until 9:45PM.
opt.add(m_end <= betty_departure)

# 5. You want to meet Betty for at least 60 minutes.
opt.add(m_end - m_start >= 60)

# To maximize your meeting time we maximize the meeting duration.
meeting_duration = m_end - m_start
h = opt.maximize(meeting_duration)

# Check and print the solution
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Convert minutes from 9:00AM to HH:MM (in 24-hour format)
    def to_time(minutes):
        hour = 9 + minutes // 60
        minute = minutes % 60
        # Adjust for PM if needed (not strictly necessary since times are given in minutes after 9:00AM)
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Richmond District at {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive Financial District at {to_time(d_val + richmond_to_financial)} (travel time = {richmond_to_financial} minutes)")
    print(f"  Meeting with Betty starts at {to_time(m_start_val)}")
    print(f"  Meeting with Betty ends at {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")