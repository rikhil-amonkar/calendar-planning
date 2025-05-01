from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_haight = 12  # Travel time from Mission District to Haight-Ashbury (in minutes)
travel_time_back = 11        # Travel time from Haight-Ashbury back to Mission District (in minutes)

# Constants for timing
arrival_time = 9 * 60             # Arrival at Mission District at 9:00 AM (540 minutes)
joshua_start = 11 * 60 + 30       # Joshua will be at Haight-Ashbury from 11:30 AM (690 minutes)
joshua_end = 22 * 60               # Joshua leaves at 10:00 PM (1200 minutes)
min_meeting_duration = 75           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_haight)  # Must arrive at Haight-Ashbury after traveling
s.add(meeting_start >= joshua_start)                           # Meeting must start after Joshua is available
s.add(meeting_start + min_meeting_duration <= joshua_end)     # Meeting must finish before Joshua leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you finish the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")