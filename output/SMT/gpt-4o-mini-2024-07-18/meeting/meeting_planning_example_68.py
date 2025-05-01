from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_russian_hill = 17  # Travel time from Haight-Ashbury to Russian Hill (in minutes)
travel_time_back = 17               # Travel time from Russian Hill back to Haight-Ashbury (in minutes)

# Constants for timing
arrival_time = 9 * 60               # Arrival at Haight-Ashbury at 9:00 AM (540 minutes)
patricia_start = 7 * 60 + 45        # Patricia will be at Russian Hill from 7:45 AM (465 minutes)
patricia_end = 14 * 60 + 15          # Patricia leaves at 2:15 PM (855 minutes)
min_meeting_duration = 30             # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_russian_hill)  # Must arrive at Russian Hill after traveling
s.add(meeting_start >= patricia_start)                              # Meeting must start after Patricia is available
s.add(meeting_start + min_meeting_duration <= patricia_end)        # Meeting must finish before Patricia leaves

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