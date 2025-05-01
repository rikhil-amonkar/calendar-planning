from z3 import *

# Create a Z3 solver instance
s = Solver()

# Travel times between locations
travel_time_to_nob_hill = 11  # Travel time from Fisherman's Wharf to Nob Hill (in minutes)
travel_time_back = 11          # Travel time from Nob Hill back to Fisherman's Wharf (in minutes)

# Constants for timing
arrival_time = 9 * 60          # Arrival at Fisherman's Wharf at 9:00 AM (540 minutes)
stephanie_start = 16 * 60 + 45  # Stephanie will be at Nob Hill from 4:45 PM (1005 minutes)
stephanie_end = 21 * 60 + 45    # Stephanie leaves Nob Hill at 9:45 PM (1305 minutes)
min_meeting_duration = 120       # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_nob_hill)  # Must arrive at Nob Hill after traveling
s.add(meeting_start >= stephanie_start)                          # Meeting must start after Stephanie is available
s.add(meeting_start + min_meeting_duration <= stephanie_end)    # Meeting must finish before Stephanie leaves

# Ensure we have enough time to return to Fisherman's Wharf after the meeting
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