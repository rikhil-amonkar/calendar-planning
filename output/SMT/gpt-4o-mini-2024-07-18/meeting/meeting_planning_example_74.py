from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_nob_hill = 17  # Travel time from Richmond District to Nob Hill (in minutes)
travel_time_back = 14          # Travel time from Nob Hill back to Richmond District (in minutes)

# Constants for timing
arrival_time = 9 * 60          # Arrival at Richmond District at 9:00 AM (540 minutes)
richard_start = 16 * 60        # Richard will be at Nob Hill from 4:00 PM (960 minutes)
richard_end = 18 * 60 + 15     # Richard leaves at 6:15 PM (1095 minutes)
min_meeting_duration = 45       # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_nob_hill)  # Must arrive at Nob Hill after traveling
s.add(meeting_start >= richard_start)                            # Meeting must start after Richard is available
s.add(meeting_start + min_meeting_duration <= richard_end)      # Meeting must finish before Richard leaves

# Add a constraint to ensure sufficient time to return after the meeting ends
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you finish the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")