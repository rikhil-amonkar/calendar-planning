from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_haight = 19  # Travel time from Bayview to Haight-Ashbury (in minutes)
travel_time_back = 18        # Travel time from Haight-Ashbury back to Bayview (in minutes)

# Constants for timing
arrival_time = 9 * 60         # Arrival at Bayview at 9:00 AM (540 minutes)
richard_start = 7 * 60        # Richard will be at Haight-Ashbury from 7:00 AM (420 minutes)
richard_end = 15 * 60 + 45    # Richard leaves at 3:45 PM (945 minutes)
min_meeting_duration = 105      # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_haight)  # Must arrive at Haight-Ashbury after traveling
s.add(meeting_start >= richard_start)                          # Meeting must start after Richard is available
s.add(meeting_start + min_meeting_duration <= richard_end)     # Meeting must finish before Richard leaves

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