from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define travel times
travel_time_to_sunset = 25  # Travel time from Nob Hill to Sunset District (in minutes)
travel_time_back = 27        # Travel time from Sunset District back to Nob Hill (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at Nob Hill at 9:00 AM (in minutes)
carol_start = 14 * 60              # Carol is at Sunset District starting at 2:00 PM (in minutes)
carol_end = 20 * 60 + 30            # Carol leaves Sunset District at 8:30 PM (in minutes)
min_meeting_duration = 75           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_sunset)  # Must arrive at Sunset after traveling
s.add(meeting_start >= carol_start)                            # Meeting must start after Carol is available
s.add(meeting_start + min_meeting_duration <= carol_end)      # Meeting must finish before Carol leaves

# Add a constraint to ensure you have enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you will finish the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")