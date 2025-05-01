from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_bayview = 26  # Travel time from Richmond District to Bayview (in minutes)
travel_time_back = 25         # Travel time from Bayview back to Richmond District (in minutes)

# Constants for timing
arrival_time = 9 * 60         # Arrival at Richmond District at 9:00 AM (540 minutes)
sarah_start = 14 * 60 + 15    # Sarah will be at Bayview from 2:15 PM (855 minutes)
sarah_end = 17 * 60 + 30      # Sarah leaves at 5:30 PM (1050 minutes)
min_meeting_duration = 45      # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_bayview)  # Must arrive at Bayview after traveling
s.add(meeting_start >= sarah_start)                             # Meeting must start after Sarah is available
s.add(meeting_start + min_meeting_duration <= sarah_end)       # Meeting must finish before Sarah leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you finish the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time to HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time to HH:MM
else:
    print("No possible trip plan found.")