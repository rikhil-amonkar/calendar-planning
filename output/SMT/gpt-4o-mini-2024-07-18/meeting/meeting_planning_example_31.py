from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_alamo = 11  # Travel time from Nob Hill to Alamo Square (in minutes)
travel_time_back = 11       # Travel time from Alamo Square back to Nob Hill (in minutes)

# Constants for timing
arrival_time = 9 * 60      # Arrival at Nob Hill at 9:00 AM (540 minutes)
anthony_start = 7 * 60 + 15  # Anthony will be at Alamo Square from 7:15 AM (435 minutes)
anthony_end = 13 * 60       # Anthony leaves at 1:00 PM (780 minutes)
min_meeting_duration = 15    # Minimum meeting duration in minutes

# Define variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_alamo)  # Must arrive at Alamo Square after traveling
s.add(meeting_start >= anthony_start)                          # Meeting must start after Anthony is available
s.add(meeting_start + min_meeting_duration <= anthony_end)    # Meeting must finish before Anthony leaves

# Add a constraint to ensure you have enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate end time of the meeting.

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")