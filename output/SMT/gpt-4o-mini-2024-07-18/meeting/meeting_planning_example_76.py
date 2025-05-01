from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_haight = 16  # Travel time from Marina District to Haight-Ashbury (in minutes)
travel_time_back = 17        # Travel time from Haight-Ashbury back to Marina District (in minutes)

# Constants for timing
arrival_time = 9 * 60        # Arrival at Marina District at 9:00 AM (540 minutes)
timothy_start = 17 * 60      # Timothy will be at Haight-Ashbury from 5:00 PM (1020 minutes)
timothy_end = 20 * 60 + 15   # Timothy leaves at 8:15 PM (1215 minutes)
min_meeting_duration = 60     # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_haight)  # Must arrive at Haight-Ashbury after traveling
s.add(meeting_start >= timothy_start)                          # Meeting must start after Timothy is available
s.add(meeting_start + min_meeting_duration <= timothy_end)    # Meeting must finish before Timothy leaves

# Add a constraint to ensure you have enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate end time of the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time to HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time to HH:MM
else:
    print("No possible trip plan found.")