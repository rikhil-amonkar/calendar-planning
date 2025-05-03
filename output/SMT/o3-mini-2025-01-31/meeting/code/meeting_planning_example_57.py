from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Bayview (in minutes after 9:00AM)
#   m_start: meeting start time at Sunset District (in minutes after 9:00AM)
#   m_end: meeting end time at Sunset District (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Bayview to Sunset District is 23 minutes.
bayview_to_sunset = 23

# Jessica's availability at Sunset District:
# 10:30AM is 90 minutes after 9:00AM.
# 5:45PM is 525 minutes after 9:00AM.
jessica_avail_from = 90
jessica_avail_until = 525

# Constraints:

# 1. You arrive at Bayview at 9:00AM, so you cannot leave before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival at Sunset District is the departure time plus travel time.
arrival_at_sunset = d + bayview_to_sunset

# 3. The meeting with Jessica can begin only after you have arrived at Sunset District,
#    and not before Jessica is available.
opt.add(m_start >= arrival_at_sunset)
opt.add(m_start >= jessica_avail_from)

# 4. The meeting must end by the time Jessica's availability ends.
opt.add(m_end <= jessica_avail_until)

# 5. You'd like to meet Jessica for a minimum of 60 minutes.
opt.add(m_end - m_start >= 60)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function to convert minutes after 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Bayview at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Sunset District at: {to_time(d_val + bayview_to_sunset)} (travel time = {bayview_to_sunset} minutes)")
    print(f"  Meeting with Jessica starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Jessica ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")