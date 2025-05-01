from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_pacific_heights = 23  # Travel time from Bayview to Pacific Heights (in minutes)
travel_time_back = 22                  # Travel time from Pacific Heights back to Bayview (in minutes)

# Constants for timing
arrival_time = 9 * 60                 # Arrival at Bayview at 9:00 AM (in minutes)
thomas_start = 12 * 60 + 15           # Thomas will be at Pacific Heights from 12:15 PM (735 minutes)
thomas_end = 17 * 60 + 15             # Thomas leaves at 5:15 PM (1035 minutes)
min_meeting_duration = 105             # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_pacific_heights)  # Must arrive at Pacific Heights after traveling
s.add(meeting_start >= thomas_start)                                  # Meeting must start after Thomas is available
s.add(meeting_start + min_meeting_duration <= thomas_end)            # Meeting must finish before Thomas leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
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