from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_mission = 17  # Travel time from Financial District to Mission District (in minutes)
travel_time_back = 17         # Travel time from Mission District back to Financial District (in minutes)

# Constants for timing
arrival_time = 9 * 60        # Arrival at Financial District at 9:00 AM (540 minutes)
william_start = 13 * 60 + 15 # William is at Mission District from 1:15 PM (795 minutes)
william_end = 14 * 60        # William leaves at 2:15 PM (840 minutes)
min_meeting_duration = 45     # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_mission)  # Must arrive at Mission after traveling
s.add(meeting_start >= william_start)                          # Meeting must start after William is available
s.add(meeting_start + min_meeting_duration <= william_end)     # Meeting must finish before William leaves

# Add a constraint to ensure you have enough time to return after the meeting is over
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