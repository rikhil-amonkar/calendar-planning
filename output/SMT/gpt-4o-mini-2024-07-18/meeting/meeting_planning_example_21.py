from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel and timing
arrival_time = 9 * 60  # Arrival at Mission District at 9:00 AM (540 minutes)
travel_time_to_haight = 12  # Travel time from Mission District to Haight-Ashbury (in minutes)
travel_time_back = 11         # Travel time from Haight-Ashbury back to Mission District (in minutes)

# Margaret's availability
margaret_start = 8 * 60  # Margaret will be at Haight-Ashbury starting at 8:00 AM (480 minutes)
margaret_end = 15 * 60 + 45  # Margaret leaves at 3:45 PM (945 minutes)
min_meeting_duration = 30    # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_haight)  # Must arrive at Haight-Ashbury after traveling
s.add(meeting_start >= margaret_start)                         # Meeting must start after Margaret is available
s.add(meeting_start + min_meeting_duration <= margaret_end)   # Meeting must finish before Margaret leaves

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