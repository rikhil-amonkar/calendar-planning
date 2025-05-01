from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for timing and travel
arrival_time = 9 * 60  # Arrival at Alamo Square at 9:00 AM (540 minutes)
travel_time_to_sunset = 16  # Travel time from Alamo Square to Sunset District (in minutes)
travel_time_back = 17        # Travel time from Sunset District back to Alamo Square (in minutes)

# Matthew's availability
matthew_start = 13 * 60 + 30  # Matthew is at Sunset District starting at 1:30 PM (810 minutes)
matthew_end = 14 * 60          # Matthew leaves at 2:30 PM (840 minutes)
min_meeting_duration = 15       # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_sunset)  # Must arrive at Sunset after travel
s.add(meeting_start >= matthew_start)                          # Meeting must start after Matthew is available
s.add(meeting_start + min_meeting_duration <= matthew_end)     # Meeting must finish before Matthew leaves

# Add a constraint to ensure there is enough time to return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you will leave the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")