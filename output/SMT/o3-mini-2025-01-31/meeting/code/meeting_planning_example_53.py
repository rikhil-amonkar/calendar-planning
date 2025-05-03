from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Richmond District (in minutes after 9:00AM)
#   m_start: meeting start time at Alamo Square (in minutes after 9:00AM)
#   m_end: meeting end time at Alamo Square (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Richmond District to Alamo Square is 13 minutes.
rd_to_as = 13

# Ashley's availability at Alamo Square:
# From 10:15AM to 1:00PM.
# 10:15AM is 75 minutes after 9:00AM.
# 1:00PM is 240 minutes after 9:00AM.
ashley_avail_from = 75
ashley_avail_until = 240

# Constraints:

# 1. You arrive at Richmond District at 9:00AM so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. It takes 13 minutes to travel from Richmond District to Alamo Square.
arrival_at_as = d + rd_to_as

# 3. The meeting with Ashley can only start after you have arrived at Alamo Square
#    and not before Ashley is available.
opt.add(m_start >= arrival_at_as)
opt.add(m_start >= ashley_avail_from)

# 4. The meeting must end by the time Ashley's availability ends.
opt.add(m_end <= ashley_avail_until)

# 5. You'd like to meet Ashley for a minimum of 120 minutes.
opt.add(m_end - m_start >= 120)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    departure_val = model[d].as_long()
    meeting_start_val = model[m_start].as_long()
    meeting_end_val = model[m_end].as_long()
    
    # Helper function: convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Richmond District at: {to_time(departure_val)} (9:00AM + {departure_val} minutes)")
    print(f"  Arrive at Alamo Square at: {to_time(departure_val + rd_to_as)} (travel time = {rd_to_as} minutes)")
    print(f"  Meeting with Ashley starts at: {to_time(meeting_start_val)}")
    print(f"  Meeting with Ashley ends at: {to_time(meeting_end_val)}")
    print(f"  Total meeting duration: {meeting_end_val - meeting_start_val} minutes")
else:
    print("No solution found.")