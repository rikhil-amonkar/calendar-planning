from z3 import Optimize, Int, Or, sat

# Helper functions for converting time strings to minutes and back.
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting.
work_start = time_to_minutes("9:00")     # 9:00 AM (540 minutes)
work_end = time_to_minutes("17:00")        # 5:00 PM (1020 minutes)

# Additional constraint: Juan cannot meet on Monday after 16:00.
juan_latest_end = time_to_minutes("16:00")  # 16:00 (960 minutes)

# Busy intervals on Monday:
# Juan is busy: 9:00 to 10:30, 15:30 to 16:00.
juan_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

# Marilyn is busy: 11:00 to 11:30, 12:30 to 13:00.
marilyn_busy = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00"))
]

# Ronald is busy: 9:00 to 10:30, 12:00 to 12:30, 13:00 to 13:30, 14:00 to 16:30.
ronald_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("16:30"))
]

# Create a solver.
opt = Optimize()

# Decision variable: meeting_start time in minutes since midnight.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting within work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Enforce Juan's constraint that he cannot meet after 16:00.
opt.add(meeting_end <= juan_latest_end)

# Function to add busy interval constraints:
def add_busy_constraints(busy_list):
    for busy_start, busy_end in busy_list:
        # The meeting must either end before the busy interval starts,
        # or start after the busy interval ends.
        opt.add(Or(meeting_end <= busy_start, meeting_start >= busy_end))

# Add busy constraints for each participant.
add_busy_constraints(juan_busy)
add_busy_constraints(marilyn_busy)
add_busy_constraints(ronald_busy)

# Objective: Schedule the meeting at the earliest possible time.
opt.minimize(meeting_start)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + meeting_duration
    print("A possible meeting time on Monday:")
    print("Start:", minutes_to_time(start_time))
    print("End:  ", minutes_to_time(end_time))
else:
    print("No valid meeting time could be found.")