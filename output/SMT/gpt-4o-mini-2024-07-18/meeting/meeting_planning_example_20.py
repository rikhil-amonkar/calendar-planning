from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_nob_hill = 8  # Travel time from Chinatown to Nob Hill (in minutes)
travel_time_back = 6          # Travel time from Nob Hill back to Chinatown (in minutes)

# Constants for timing
arrival_time = 9 * 60         # Arrival at Chinatown at 9:00 AM (540 minutes)
joseph_start = 11 * 60 + 30   # Joseph is at Nob Hill starting at 11:30 AM (690 minutes)
joseph_end = 15 * 60 + 15      # Joseph leaves at 3:15 PM (915 minutes)
min_meeting_duration = 75       # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_nob_hill)  # Must arrive at Nob Hill after traveling
s.add(meeting_start >= joseph_start)                             # Meeting must start after Joseph is available
s.add(meeting_start + min_meeting_duration <= joseph_end)       # Meeting must finish before Joseph leaves

# Add a constraint to ensure there's enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you will finish the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")