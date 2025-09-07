from z3 import Int, Optimize, Or, sat

# Meeting parameters (in minutes)
meeting_duration = 30
start_work = 9 * 60         # 9:00 -> 540 minutes
end_work = 17 * 60          # 17:00 -> 1020 minutes

# Define busy intervals (start, end) in minutes from midnight.
# Adam's busy intervals
adam_busy = [
    (9 * 60 + 30, 10 * 60),   # 9:30 - 10:00
    (12 * 60 + 30, 13 * 60),  # 12:30 - 13:00
    (14 * 60 + 30, 15 * 60),  # 14:30 - 15:00
    (16 * 60 + 30, 17 * 60)   # 16:30 - 17:00
]

# Roy's busy intervals
roy_busy = [
    (10 * 60, 11 * 60),          # 10:00 - 11:00
    (11 * 60 + 30, 13 * 60),     # 11:30 - 13:00
    (13 * 60 + 30, 14 * 60 + 30), # 13:30 - 14:30
    (16 * 60 + 30, 17 * 60)      # 16:30 - 17:00
]

# Initialize the optimizer
opt = Optimize()
start = Int('start')

# Constraint: The meeting must be scheduled within work hours.
opt.add(start >= start_work)
opt.add(start + meeting_duration <= end_work)

# Helper function: For each busy interval, ensure that the meeting does not overlap.
def add_non_overlap_constraints(solver, meeting_start, duration, busy_intervals):
    for (busy_start, busy_end) in busy_intervals:
        # The meeting interval [start, start+duration) must lie entirely either
        # before the busy interval or after the busy interval.
        solver.add(Or(meeting_start + duration <= busy_start, meeting_start >= busy_end))

# Add non-overlap constraints for Adam and Roy.
add_non_overlap_constraints(opt, start, meeting_duration, adam_busy)
add_non_overlap_constraints(opt, start, meeting_duration, roy_busy)

# Set objective to minimize the meeting start time (i.e. the earliest possible meeting)
opt.minimize(start)

# Check for a solution.
result = opt.check()
if result == sat:
    model = opt.model()
    meeting_start_val = model[start].as_long()
    meeting_end_val = meeting_start_val + meeting_duration

    # Helper function: converts minutes since midnight to an HH:MM string format.
    def minutes_to_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_str = minutes_to_str(meeting_start_val)
    end_str = minutes_to_str(meeting_end_val)
    
    print("Monday", f"{start_str}-{end_str}")
else:
    print("No available meeting time found.")