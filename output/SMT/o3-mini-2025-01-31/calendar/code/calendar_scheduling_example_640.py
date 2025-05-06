from z3 import Optimize, Int, Or, If, sat

# Helper functions for time conversion.
def time_to_minutes(t):
    # Convert "HH:MM" to minutes since midnight.
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    # Convert minutes since midnight to "HH:MM" string.
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Meeting configuration.
meeting_duration = 30  # 30-minute meeting.
work_start = time_to_minutes("9:00")   # 9:00 AM = 540 minutes.
work_end   = time_to_minutes("17:00")   # 17:00 = 1020 minutes.

# Allowed days: Monday = 0, Tuesday = 1.
allowed_days = [0, 1]

# Busy intervals for Bobby.
# Bobby's busy schedule:
# Monday: 14:30 to 15:00.
# Tuesday: 9:00 to 11:30; 12:00 to 12:30; 13:00 to 15:00; 15:30 to 17:00.
bobby_busy = {
    0: [
        (time_to_minutes("14:30"), time_to_minutes("15:00"))
    ],
    1: [
        (time_to_minutes("9:00"),  time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("17:00"))
    ]
}

# Busy intervals for Michael.
# Michael's busy schedule:
# Monday: 9:00 to 10:00; 10:30 to 13:30; 14:00 to 15:00; 15:30 to 17:00.
# Tuesday: 9:00 to 10:30; 11:00 to 11:30; 12:00 to 14:00; 15:00 to 16:00; 16:30 to 17:00.
michael_busy = {
    0: [
        (time_to_minutes("9:00"),  time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("17:00"))
    ],
    1: [
        (time_to_minutes("9:00"),  time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("14:00")),
        (time_to_minutes("15:00"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

# Initialize the Z3 Optimize solver.
opt = Optimize()

# Decision variables:
# meeting_day: 0 for Monday, 1 for Tuesday.
meeting_day = Int("meeting_day")
opt.add(Or([meeting_day == d for d in allowed_days]))

# meeting_start: start time (in minutes since midnight) for the meeting on the chosen day.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain meeting time to lie within the work hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# Function to add busy interval constraints for a given participant's schedule.
def add_busy_constraints(schedule):
    for day, intervals in schedule.items():
        for b_start, b_end in intervals:
            # If the meeting is on this day, it must not overlap with this busy interval.
            opt.add(If(meeting_day == day, 
                       Or(meeting_end <= b_start, meeting_start >= b_end),
                       True))

# Add busy constraints for both Bobby and Michael.
add_busy_constraints(bobby_busy)
add_busy_constraints(michael_busy)

# Objective: schedule the meeting at the earliest available time.
# We minimize overall time defined as (meeting_day * 1440 + meeting_start)
overall_time = meeting_day * 1440 + meeting_start
opt.minimize(overall_time)

# Solve the scheduling problem.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    chosen_start = model[meeting_start].as_long()
    chosen_end = chosen_start + meeting_duration

    day_names = {0: "Monday", 1: "Tuesday"}
    
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(chosen_start))
    print("End:   ", minutes_to_time(chosen_end))
else:
    print("No valid meeting time could be found.")