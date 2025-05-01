from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_nob_hill = 12  # Travel time from Marina District to Nob Hill (in minutes)
travel_time_back = 11          # Travel time from Nob Hill back to Marina District (in minutes)

# Constants for timing
arrival_time = 9 * 60             # Arrival at Marina District at 9:00 AM (540 minutes)
daniel_start = 19 * 60 + 45       # Daniel will be at Nob Hill from 7:45 PM (1185 minutes)
daniel_end = 21 * 60               # Daniel leaves at 9:00 PM (1260 minutes)
min_meeting_duration = 15          # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_nob_hill)  # Must arrive at Nob Hill after traveling
s.add(meeting_start >= daniel_start)                            # Meeting must start after Daniel is available
s.add(meeting_start + min_meeting_duration <= daniel_end)      # Meeting must finish before Daniel leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")