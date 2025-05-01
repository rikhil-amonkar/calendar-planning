from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_nob_hill = 27  # Travel time from Sunset District to Nob Hill (in minutes)
travel_time_back = 25          # Travel time from Nob Hill back to Sunset District (in minutes)

# Constants for timing
arrival_time = 9 * 60         # Arrival at Sunset District at 9:00 AM (540 minutes)
rebecca_start = 9 * 60        # Rebecca will be at Nob Hill from 9:00 AM (540 minutes)
rebecca_end = 18 * 60 + 15    # Rebecca leaves at 6:15 PM (1115 minutes)
min_meeting_duration = 30      # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_nob_hill)  # Must arrive at Nob Hill after traveling
s.add(meeting_start >= rebecca_start)                            # Meeting must start after Rebecca is available
s.add(meeting_start + min_meeting_duration <= rebecca_end)      # Meeting must finish before Rebecca leaves

# Ensure there is enough time to return to Sunset District after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you finish the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")