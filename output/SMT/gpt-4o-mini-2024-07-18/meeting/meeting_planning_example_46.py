from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_north_beach = 19  # Travel time from Haight-Ashbury to North Beach (in minutes)
travel_time_back = 18              # Travel time from North Beach back to Haight-Ashbury (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at Haight-Ashbury at 9:00 AM (540 minutes)
robert_start = 16 * 60 + 30        # Robert will be at North Beach from 4:30 PM (990 minutes)
robert_end = 21 * 60 + 30          # Robert leaves at 9:30 PM (1290 minutes)
min_meeting_duration = 90           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_north_beach)  # Must arrive at North Beach after traveling
s.add(meeting_start >= robert_start)                                # Meeting must start after Robert is available
s.add(meeting_start + min_meeting_duration <= robert_end)          # Meeting must finish before Robert leaves

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