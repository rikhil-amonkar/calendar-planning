from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define travel times
travel_time_to_north_beach = 18  # Travel time from Presidio to North Beach (in minutes)
travel_time_back = 17              # Travel time from North Beach back to Presidio (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at Presidio at 9:00 AM (540 minutes)
betty_start = 18 * 60 + 45         # Betty is at North Beach from 6:45 PM (1125 minutes)
betty_end = 22 * 60                 # Betty leaves at 10:00 PM (1200 minutes)
min_meeting_duration = 75           # Minimum meeting duration (in minutes)

# Define variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_north_beach)  # Must arrive at North Beach after travel
s.add(meeting_start >= betty_start)                                # Meeting must start after Betty is available
s.add(meeting_start + min_meeting_duration <= betty_end)          # Meeting must finish before Betty leaves

# Add a constraint to ensure you have enough time to return after the meeting
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