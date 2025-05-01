from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_alamo = 13  # Travel time from Richmond District to Alamo Square (in minutes)
travel_time_back = 12       # Travel time from Alamo Square back to Richmond District (in minutes)

# Constants for timing
arrival_time = 9 * 60        # Arrival at Richmond District at 9:00 AM (540 minutes)
ashley_start = 10 * 60 + 15  # Ashley will be at Alamo Square from 10:15 AM (615 minutes)
ashley_end = 13 * 60         # Ashley leaves at 1:00 PM (780 minutes)
min_meeting_duration = 120     # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_alamo)  # Must arrive at Alamo Square after traveling
s.add(meeting_start >= ashley_start)                          # Meeting must start after Ashley is available
s.add(meeting_start + min_meeting_duration <= ashley_end)    # Meeting must finish before Ashley leaves

# Add a constraint to ensure there is enough time to return after the meeting ends
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