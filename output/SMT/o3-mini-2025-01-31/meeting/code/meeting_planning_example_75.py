from z3 import Optimize, Int, sat

# Create an optimizer instance.
opt = Optimize()

# All times are measured in minutes after 9:00AM.
# Variables:
#   d      : departure time from Pacific Heights (in minutes after 9:00AM)
#   m_start: meeting start time at Fisherman's Wharf (in minutes after 9:00AM)
#   m_end  : meeting end time at Fisherman's Wharf (in minutes after 9:00AM)
d = Int('d')
m_start = Int('m_start')
m_end = Int('m_end')

# Given travel time from Pacific Heights to Fisherman's Wharf is 13 minutes.
pac_heights_to_fw = 13

# David's availability at Fisherman's Wharf:
# 11:30AM -> 150 minutes after 9:00AM.
# 2:45PM  -> 345 minutes after 9:00AM.
david_avail_from = 150
david_avail_until = 345

# CONSTRAINTS:

# 1. You arrive at Pacific Heights at 9:00AM, so you cannot depart before 9:00AM.
opt.add(d >= 0)

# 2. Your arrival time at Fisherman's Wharf is your departure time plus travel time.
arrival_at_fw = d + pac_heights_to_fw

# 3. The meeting with David can only start after you arrive at Fisherman's Wharf 
#    and not before David is available.
opt.add(m_start >= arrival_at_fw)
opt.add(m_start >= david_avail_from)

# 4. The meeting must finish by the end of David's availability.
opt.add(m_end <= david_avail_until)

# 5. You'd like to meet David for at least 15 minutes.
opt.add(m_end - m_start >= 15)

# Objective: maximize the meeting duration.
meeting_duration = m_end - m_start
opt.maximize(meeting_duration)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    d_val = model[d].as_long()
    m_start_val = model[m_start].as_long()
    m_end_val = model[m_end].as_long()
    
    # Helper function: converts minutes after 9:00AM into HH:MM format.
    def to_time(minutes_after_9):
        total_minutes = 9 * 60 + minutes_after_9
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    print("Optimal Schedule:")
    print(f"  Depart Pacific Heights at: {to_time(d_val)} (9:00AM + {d_val} minutes)")
    print(f"  Arrive at Fisherman's Wharf at: {to_time(d_val + pac_heights_to_fw)} (travel time = {pac_heights_to_fw} minutes)")
    print(f"  Meeting with David starts at: {to_time(m_start_val)}")
    print(f"  Meeting with David ends at: {to_time(m_end_val)}")
    print(f"  Total meeting duration: {m_end_val - m_start_val} minutes")
else:
    print("No solution found.")