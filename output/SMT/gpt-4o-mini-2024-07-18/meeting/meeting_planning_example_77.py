from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_golden_gate = 9  # Travel time from Richmond District to Golden Gate Park (in minutes)
travel_time_back = 7              # Travel time from Golden Gate Park back to Richmond District (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival time at Richmond District (9:00 AM, 540 minutes)
robert_start = 8 * 60 + 15         # Robert will be at Golden Gate Park from 8:15 AM (495 minutes)
robert_end = 20 * 60 + 30          # Robert leaves at 8:30 PM (1230 minutes)
min_meeting_duration = 30           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_golden_gate)  # Must arrive at Golden Gate Park
s.add(meeting_start >= robert_start)                               # Meeting must start after Robert is available
s.add(meeting_start + min_meeting_duration <= robert_end)         # Meeting must finish before Robert leaves

# Ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you finish the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time to HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time to HH:MM
else:
    print("No possible trip plan found.")