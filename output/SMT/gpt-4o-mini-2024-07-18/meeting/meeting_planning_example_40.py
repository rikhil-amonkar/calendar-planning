from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_sunset = 17  # Travel time from The Castro to Sunset District (in minutes)
travel_time_back = 17        # Travel time from Sunset District back to The Castro (in minutes)

# Constants for timing
arrival_time = 9 * 60  # Arrival at The Castro at 9:00 AM (540 minutes)
deborah_start = 14 * 60 + 15  # Deborah will be at Sunset District from 2:15 PM (855 minutes)
deborah_end = 20 * 60          # Deborah leaves at 8:00 PM (1200 minutes)
min_meeting_duration = 75       # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_sunset)  # Must arrive at Sunset District after traveling
s.add(meeting_start >= deborah_start)                          # Meeting must start after Deborah is available
s.add(meeting_start + min_meeting_duration <= deborah_end)    # Meeting must finish before Deborah leaves

# Add a constraint to ensure there is enough time to return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate the end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")