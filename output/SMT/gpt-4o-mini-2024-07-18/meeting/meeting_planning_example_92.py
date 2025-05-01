from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_castro = 23  # Travel time from Financial District to The Castro (in minutes)
travel_time_back = 20         # Travel time from The Castro back to Financial District (in minutes)

# Constants for timing
arrival_time = 9 * 60             # Arrival at Financial District at 9:00 AM (540 minutes)
carol_start = 14 * 60             # Carol will be at The Castro from 2:00 PM (840 minutes)
carol_end = 17 * 60 + 45          # Carol leaves at 5:45 PM (1065 minutes)
min_meeting_duration = 45          # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_castro)  # Must arrive at The Castro after traveling
s.add(meeting_start >= carol_start)                            # Meeting must start after Carol is available
s.add(meeting_start + min_meeting_duration <= carol_end)      # Meeting must finish before Carol leaves

# Ensure there's enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time to HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time to HH:MM
else:
    print("No possible trip plan found.")