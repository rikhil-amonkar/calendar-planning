from z3 import *

# Meeting duration (in minutes)
duration = 30

# Define meeting variables:
# meeting_day: 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# Robert prefers not to have more meetings on Monday, so we will force day != Monday.
meeting_day = Int("meeting_day")
meeting_start = Int("meeting_start")  # number of minutes from 9:00

# Create an Optimize solver to support lexicographic minimization.
opt = Optimize()

# Allowed days: Only Tuesday (1) and Wednesday (2).
opt.add(Or(meeting_day == 1, meeting_day == 2))
# Meeting must start between 9:00 and 16:30 so that it ends by 17:00.
opt.add(meeting_start >= 0, meeting_start + duration <= 480)

# Busy schedules (times are represented as minutes after 9:00)
# For example, 11:00 is 120 and 11:30 is 150.
robert_busy = {
    0: [(120, 150), (300, 330), (390, 420)],  # Monday
    1: [(90, 120), (360, 390)],                # Tuesday
    2: [(60, 120), (150, 180), (210, 240), (270, 300), (360, 390), (420, 450)]  # Wednesday
}

ralph_busy = {
    0: [(60, 270), (300, 330), (360, 480)],    # Monday
    1: [(0, 30), (60, 90), (120, 150), (180, 240), (300, 390), (420, 480)],      # Tuesday
    2: [(90, 120), (150, 180), (240, 330), (450, 480)]  # Wednesday
}

# For each busy interval on a day, ensure the meeting (if scheduled on that day)
# does not overlap with that interval. Overlap is avoided if:
# either meeting ends <= busy_start or meeting starts >= busy_end.
def add_busy_constraints(busy_dict):
    for day, intervals in busy_dict.items():
        for (b_start, b_end) in intervals:
            opt.add(Implies(meeting_day == day,
                            Or(meeting_start + duration <= b_start,
                               meeting_start >= b_end)))

# Add constraints for each participant.
add_busy_constraints(robert_busy)
add_busy_constraints(ralph_busy)

# We want the earliest time available (first by day, then by meeting start time).
# Since Robert prefers to avoid Monday, we already limited days to Tuesday (1) and Wednesday (2).
h1 = opt.minimize(meeting_day)
h2 = opt.minimize(meeting_start)

# Check for a solution and display the result.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    chosen_start = model[meeting_start].as_long()
    
    # Map numeric day to day names.
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    day_str = day_names.get(chosen_day, "Unknown")
    
    # Convert meeting_start (minutes after 9:00) into actual HH:MM.
    start_total = 9 * 60 + chosen_start
    start_hour = start_total // 60
    start_minute = start_total % 60
    
    # Meeting end time calculation.
    end_total = start_total + duration
    end_hour = end_total // 60
    end_minute = end_total % 60

    # Format the time as "HH:MM:HH:MM"
    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    print(day_str, time_str)
else:
    print("No available time slot found.")