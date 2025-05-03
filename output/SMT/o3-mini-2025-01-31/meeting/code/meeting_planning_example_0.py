from z3 import Optimize, Int, sat

# Create an optimizer
opt = Optimize()

# Time is measured in minutes after 9:00AM.
# d: departure time from Marina District (in minutes after 9:00AM)
# m_start: actual meeting start time at Mission District (in minutes after 9:00AM)
# m_end: actual meeting end time at Mission District (in minutes after 9:00AM)

d = Int('d')         # departure time from Marina
m_start = Int('m_start')   # meeting start time with Stephanie
m_end = Int('m_end')       # meeting end time with Stephanie

# Given travel times in minutes:
marina_to_mission = 20   # minutes from Marina -> Mission

# Stephanie is available in the Mission District from 10:30AM to 1:30PM.
# In minutes after 9:00AM, these are:
stephanie_arrival = 90   # 10:30AM is 90 minutes after 9:00AM
stephanie_departure = 270  # 1:30PM is 270 minutes after 9:00AM

# Constraints:
# 1. You arrive at Marina at 9:00AM so you can only leave Marina after time 0.
opt.add(d >= 0)
# 2. You travel from Marina to Mission District: travel takes 20 minutes.
arrival_at_mission = d + marina_to_mission
# 3. You cannot start meeting Stephanie until you have arrived and until she is available.
opt.add(m_start >= arrival_at_mission)
opt.add(m_start >= stephanie_arrival)
# 4. Stephanie will be in Mission only until 1:30PM.
opt.add(m_end <= stephanie_departure)
# 5. You want to meet Stephanie for at least 120 minutes.
opt.add(m_end - m_start >= 120)

# To "optimize your goals" (i.e. meet as many minutes as possible with your friend)
# we maximize the meeting duration.
meeting_duration = m_end - m_start
h = opt.maximize(meeting_duration)

# Check and print the solution
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Convert minutes from 9:00AM to HH:MM format
    def to_time(minutes):
        hour = 9 + minutes // 60
        minute = minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Marina at {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive Mission at {to_time(d_val + marina_to_mission)} (travel time = {marina_to_mission} minutes)")
    print(f"  Meeting starts at {to_time(m_start_val)}")
    print(f"  Meeting ends at {to_time(m_end_val)}")
    print(f"  Meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")