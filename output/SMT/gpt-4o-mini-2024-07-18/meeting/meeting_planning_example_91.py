from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_richmond = 14  # Travel time from Russian Hill to Richmond District (in minutes)
travel_time_back = 13          # Travel time from Richmond District back to Russian Hill (in minutes)

# Constants for timing
arrival_time = 9 * 60          # Arrival at Russian Hill at 9:00 AM (540 minutes)
daniel_start = 19 * 60         # Daniel will be at Richmond District from 7:00 PM (1140 minutes)
daniel_end = 20 * 60 + 15      # Daniel leaves at 8:15 PM (1215 minutes)
min_meeting_duration = 75       # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_richmond)  # Must arrive at Richmond District after traveling
s.add(meeting_start >= daniel_start)                            # Meeting must start after Daniel is available
s.add(meeting_start + min_meeting_duration <= daniel_end)      # Meeting must finish before Daniel leaves

# Add a constraint to ensure enough time to return after the meeting is over
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