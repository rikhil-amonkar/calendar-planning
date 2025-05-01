from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times and availability
travel_time_to_presidio = 7  # Travel time from Richmond District to Presidio (in minutes)
travel_time_back = 7          # Travel time from Presidio back to Richmond District (in minutes)

# Constants for timing
arrival_time = 9 * 60         # Arrival at Richmond District at 9:00 AM (540 minutes)
sarah_start = 13 * 60 + 15    # Sarah will be at Presidio from 1:15 PM (795 minutes)
sarah_end = 15 * 60 + 15      # Sarah leaves at 3:15 PM (915 minutes)
min_meeting_duration = 105     # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_presidio)  # Must arrive at Presidio after traveling
s.add(meeting_start >= sarah_start)                            # Meeting must start after Sarah is available
s.add(meeting_start + min_meeting_duration <= sarah_end)      # Meeting must finish before Sarah leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you finish the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")