from z3 import Int, Optimize, Or

# Meeting parameters (in minutes)
meeting_duration = 30
start_work = 9 * 60         # 9:00 in minutes (540)
end_work = 17 * 60          # 17:00 in minutes (1020)

# Define busy intervals (start time, end time) in minutes from midnight
# Adam's busy intervals
adam_busy = [
    (9 * 60 + 30, 10 * 60),   # 9:30 - 10:00
    (12 * 60 + 30, 13 * 60),  # 12:30 - 13:00
    (14 * 60 + 30, 15 * 60),  # 14:30 - 15:00
    (16 * 60 + 30, 17 * 60)   # 16:30 - 17:00
]

# Roy's busy intervals
roy_busy = [
    (10 * 60, 11 * 60),       # 10:00 - 11:00
    (11 * 60 + 30, 13 * 60),  # 11:30 - 13:00
    (13 * 60 + 30, 14 * 60 + 30),  # 13:30 - 14:30
    (16 * 60 + 30, 17 * 60)   # 16:30 - 17:00
]

# Initialize the optimizer
opt = Optimize()
start = Int('start')

# Constraint: Meeting must be within work hours.
opt.add(start >= start_work)
opt.add(start + meeting_duration <= end_work)

# Helper: Add non-overlap constraints for a given list of busy intervals.
def add_non_overlap_constraints(solver, meeting_start, duration, busy_intervals):
    for (busy_start, busy_end) in busy_intervals:
        # Meeting [start, start+duration) must not overlap with [busy_start, busy_end)
        solver.add(Or(meeting_start + duration <= busy_start, meeting_start >= busy_end))

add_non_overlap_constraints(opt, start, meeting_duration, adam_busy)
add_non_overlap_constraints(opt, start, meeting_duration, roy_busy)

# Set objective to minimize the meeting start time (earliest meeting)
opt.minimize(start)

# Check for a solution and extract it if available
if opt.check() == 'sat':
    model = opt.model()
    meeting_start = model[start].as_long()
    meeting_end = meeting_start + meeting_duration

    # Convert minutes to HH:MM string format.
    def minutes_to_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_str = minutes_to_str(meeting_start)
    end_str = minutes_to_str(meeting_end)
    
    print("Monday", f"{start_str}:{end_str}")
else:
    print("No available meeting time found.")