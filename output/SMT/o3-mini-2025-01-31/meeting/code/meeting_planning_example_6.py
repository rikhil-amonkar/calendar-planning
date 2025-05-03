from z3 import Optimize, Int, sat

# Create an optimizer for the scheduling problem.
opt = Optimize()

# Define variables:
# d: departure time from Fisherman's Wharf (in minutes after 9:00AM)
# m_start: meeting start time at Nob Hill (in minutes after 9:00AM)
# m_end: meeting end time at Nob Hill (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time: Fisherman's Wharf to Nob Hill takes 11 minutes.
fwharf_to_nobhill = 11

# Kenneth's availability at Nob Hill:
# 2:15PM -> 5 hours 15 minutes after 9:00AM = 315 minutes
# 7:45PM -> 10 hours 45 minutes after 9:00AM = 645 minutes
kenneth_arrival = 315
kenneth_departure = 645

# Constraints:
# 1. You arrive at Fisherman's Wharf at 9:00AM, so you cannot depart before that.
opt.add(d >= 0)

# 2. Travel time: arriving at Nob Hill is departure time plus 11 minutes.
arrival_at_nobhill = d + fwharf_to_nobhill

# 3. You cannot begin the meeting until you've arrived at Nob Hill and until Kenneth is present.
opt.add(m_start >= arrival_at_nobhill)
opt.add(m_start >= kenneth_arrival)

# 4. Kenneth leaves Nob Hill at 7:45PM.
opt.add(m_end <= kenneth_departure)

# 5. You want to meet Kenneth for at least 90 minutes.
opt.add(m_end - m_start >= 90)

# Objective: Maximize the meeting duration.
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
    print(f"  Depart Fisherman's Wharf at {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Nob Hill at {to_time(d_val + fwharf_to_nobhill)} (travel time = {fwharf_to_nobhill} minutes)")
    print(f"  Meeting with Kenneth starts at {to_time(m_start_val)}")
    print(f"  Meeting with Kenneth ends at {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")