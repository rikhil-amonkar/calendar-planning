from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_nob_hill = 17  # Travel time from Richmond District to Nob Hill (in minutes)
travel_time_back = 14          # Travel time from Nob Hill back to Richmond District (in minutes)

# Constants for timing
arrival_time = 9 * 60          # Arrival at Richmond District at 9:00 AM (540 minutes)
paul_start = 9 * 60 + 30       # Paul will be at Nob Hill from 9:30 AM (570 minutes)
paul_end = 11 * 60 + 15        # Paul leaves at 11:15 AM (675 minutes)
min_meeting_duration = 15       # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_nob_hill)  # Must arrive at Nob Hill after travelling
s.add(meeting_start >= paul_start)                               # Meeting must start after Paul is available
s.add(meeting_start + min_meeting_duration <= paul_end)         # Meeting must finish before Paul leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you will finish the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time to HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time to HH:MM
else:
    print("No possible trip plan found.")