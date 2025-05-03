from z3 import Optimize, Int, sat

# Create the optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d: departure time from Pacific Heights (in minutes after 9:00AM)
#   m_start: meeting start time at Fisherman's Wharf (in minutes after 9:00AM)
#   m_end: meeting end time at Fisherman's Wharf (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Pacific Heights to Fisherman's Wharf is 13 minutes.
ph_to_fw = 13

# Betty's availability at Fisherman's Wharf:
# 8:45AM corresponds to -15 minutes after 9:00AM.
# 6:00PM corresponds to 540 minutes after 9:00AM (9 hours * 60 = 540).
betty_avail_from = -15
betty_avail_until = 540

# Constraints

# 1. You arrive at Pacific Heights at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Travel time: arrival at Fisherman's Wharf is d + 13 minutes.
arrival_at_fw = d + ph_to_fw

# 3. The meeting with Betty cannot start until you have arrived at Fisherman's Wharf.
# Also, Betty is available starting at 8:45AM, but since you'll arrive after 9:00, the meeting starts at your arrival.
opt.add(m_start >= arrival_at_fw)
# (No need to check m_start >= betty_avail_from, as arrival time will always be >= 0.)

# 4. The meeting must finish by Betty's availability end time (6:00PM).
opt.add(m_end <= betty_avail_until)

# 5. You'd like to meet Betty for a minimum of 105 minutes.
opt.add(m_end - m_start >= 105)

# Objective: maximize the meeting duration (m_end - m_start).
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val      = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val   = model[m_end].as_long()

    # Helper function: convert minutes after 9:00AM to HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Pacific Heights at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Fisherman's Wharf at: {to_time(d_val + ph_to_fw)} (travel time = {ph_to_fw} minutes)")
    print(f"  Meeting with Betty starts at: {to_time(m_start_val)}")
    print(f"  Meeting with Betty ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")