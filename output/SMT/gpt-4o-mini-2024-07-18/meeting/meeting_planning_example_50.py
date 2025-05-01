from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_nob_hill = 7  # Travel time from North Beach to Nob Hill (in minutes)
travel_time_back = 8          # Travel time from Nob Hill back to North Beach (in minutes)

# Constants for timing
arrival_time = 9 * 60        # Arrival at North Beach at 9:00 AM (540 minutes)
melissa_start = 9 * 60 + 30  # Melissa will be at Nob Hill from 9:30 AM (570 minutes)
melissa_end = 20 * 60 + 30    # Melissa leaves at 8:30 PM (1230 minutes)
min_meeting_duration = 75      # Minimum meeting duration (in minutes)

# Define variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_nob_hill)  # Must arrive at Nob Hill after traveling
s.add(meeting_start >= melissa_start)                            # Meeting must start after Melissa is available
s.add(meeting_start + min_meeting_duration <= melissa_end)      # Meeting must finish before Melissa leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when meeting ends

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time to HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time to HH:MM
else:
    print("No possible trip plan found.")