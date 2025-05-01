from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define travel times
travel_time_to_sunset = 23  # Travel time from Bayview to Sunset District (in minutes)
travel_time_back = 22        # Travel time from Sunset District back to Bayview (in minutes)

# Constants for timing
arrival_time = 9 * 60          # Arrival at Bayview at 9:00 AM (540 minutes)
jessica_start = 10 * 60 + 30   # Jessica will be at Sunset District from 10:30 AM (630 minutes)
jessica_end = 17 * 60 + 45     # Jessica leaves at 5:45 PM (1065 minutes)
min_meeting_duration = 60       # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_sunset)  # Must arrive at Sunset District after traveling
s.add(meeting_start >= jessica_start)                          # Meeting must start after Jessica is available
s.add(meeting_start + min_meeting_duration <= jessica_end)     # Meeting must finish before Jessica leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
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