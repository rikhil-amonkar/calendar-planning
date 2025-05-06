from z3 import Optimize, Int, Or, Implies, sat

# Helper functions to convert time strings.
def time_to_minutes(t):
    # Converts "HH:MM" to minutes since midnight.
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    # Converts minutes since midnight back to "HH:MM" format.
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Meeting configuration.
meeting_duration = 30  # in minutes
work_start = time_to_minutes("9:00")   # 9:00 => 540 minutes
work_end   = time_to_minutes("17:00")   # 17:00 => 1020 minutes

# Allowed meeting days: Monday (0), Tuesday (1), Wednesday (2).
# Decision variable for meeting day.
meeting_day = Int("meeting_day")
# Constrain meeting_day to be 0, 1, or 2.
allowed_days = [0, 1, 2]

# Add constraint for allowed days.
constraints = [meeting_day == d for d in allowed_days]
# Instead of joining by OR in a loop, we add an explicit constraint:
# meeting_day ∈ {0,1,2}
# We'll add this constraint below via an Or:
day_constraint = Or(meeting_day == allowed_days[0],
                    meeting_day == allowed_days[1],
                    meeting_day == allowed_days[2])

# Create the solver
opt = Optimize()
opt.add(day_constraint)

# Decision variable for meeting start time in minutes since midnight.
meeting_start = Int("meeting_start")
meeting_end = meeting_start + meeting_duration

# Constrain the meeting within working hours.
opt.add(meeting_start >= work_start, meeting_end <= work_end)

# John's personal preference:
# On Monday (day==0), John would like to avoid meetings after 14:30.
# We enforce that if meeting is on Monday, it must end by 14:30.
john_monday_deadline = time_to_minutes("14:30")
opt.add(Implies(meeting_day == 0, meeting_end <= john_monday_deadline))

# Jennifer's busy intervals per day:
# Monday busy intervals.
jennifer_monday_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:30")),
    (time_to_minutes("15:00"), time_to_minutes("17:00"))
]

# Tuesday busy intervals.
jennifer_tuesday_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("17:00"))
]

# Wednesday busy intervals.
jennifer_wednesday_busy = [
    (time_to_minutes("9:00"),  time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Helper function to add non-overlapping busy interval constraints.
def add_busy_intervals(day_value, busy_intervals):
    for b_start, b_end in busy_intervals:
        # If meeting is on the specific day, then the meeting must not overlap the busy interval.
        opt.add(Implies(meeting_day == day_value,
                        Or(meeting_end <= b_start, meeting_start >= b_end)))

# Add Jennifer's busy interval constraints for each day.
add_busy_intervals(0, jennifer_monday_busy)
add_busy_intervals(1, jennifer_tuesday_busy)
add_busy_intervals(2, jennifer_wednesday_busy)

# John has no busy intervals aside from his preference on Monday.

# Objective: schedule the meeting at the earliest availability.
# We combine the day and time into a single objective. Lower day (Monday < Tuesday < Wednesday)
# and earlier meeting_start are preferred.
opt.minimize(meeting_day * 10000 + meeting_start)

if opt.check() == sat:
    model = opt.model()
    chosen_day = model[meeting_day].as_long()
    start_val = model[meeting_start].as_long()
    end_val = start_val + meeting_duration
    
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    print("A possible meeting time:")
    print("Day:   ", day_names[chosen_day])
    print("Start: ", minutes_to_time(start_val))
    print("End:   ", minutes_to_time(end_val))
else:
    print("No valid meeting time could be found.")