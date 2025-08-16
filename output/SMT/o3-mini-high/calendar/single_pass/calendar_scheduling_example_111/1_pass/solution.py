from z3 import Int, Solver, Or, sat

# We represent time in minutes with 9:00 as minute 0.
# The working day is from 9:00 (0 minutes) to 17:00 (480 minutes).
# The meeting is 30 minutes long, so the start time must be between 0 and 450.
meeting_duration = 30
s = Int('s')  # meeting start time in minutes offset from 9:00

solver = Solver()
# Meeting must start and end within the workday:
solver.add(s >= 0, s + meeting_duration <= 480)

# Convert meeting times to offsets relative to 9:00.
# For example, 9:00 is 0, 10:00 is 60, 17:00 is 480, etc.

# Gregory's blocked times:
#   9:00 - 10:00  => [0, 60)
#   10:30 - 11:30 => [90, 150)
#   12:30 - 13:00 => [210, 240)
#   13:30 - 14:00 => [270, 300)
gregory_blocks = [(0, 60), (90, 150), (210, 240), (270, 300)]

# Natalie's calendar is wide open (no blocked intervals)
natalie_blocks = []

# Christine's blocked times:
#   9:00 - 11:30  => [0, 150)
#   13:30 - 17:00 => [270, 480)
christine_blocks = [(0, 150), (270, 480)]

# Vincent's blocked times:
#   9:00 - 9:30   => [0, 30)
#   10:30 - 12:00 => [90, 180)
#   12:30 - 14:00 => [210, 300)
#   14:30 - 17:00 => [330, 480)
vincent_blocks = [(0, 30), (90, 180), (210, 300), (330, 480)]

# For each blocked interval, the meeting [s, s+30] must not overlap with it:
def add_no_overlap_constraints(blocks):
    for (block_start, block_end) in blocks:
        # The meeting does not intersect the block if it ends before the block
        # starts or starts after the block ends.
        solver.add(Or(s + meeting_duration <= block_start, s >= block_end))

# Add constraints from each participant
add_no_overlap_constraints(gregory_blocks)
add_no_overlap_constraints(christine_blocks)
add_no_overlap_constraints(vincent_blocks)
# Natalie has no blocks

if solver.check() == sat:
    m = solver.model()[s].as_long()
    meeting_start = m         # in minutes offset from 9:00
    meeting_end = meeting_start + meeting_duration  # meeting end time in minutes offset from 9:00

    # Helper function to convert minutes offset to a HH:MM string in 24-hour format.
    def convert_time(minutes_offset):
        total_minutes = minutes_offset + 9 * 60  # because 9:00 is the start
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    start_time_str = convert_time(meeting_start)
    end_time_str = convert_time(meeting_end)

    # Print the result in the required format.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: " + start_time_str)
    print("End Time: " + end_time_str)
else:
    print("No solution found")