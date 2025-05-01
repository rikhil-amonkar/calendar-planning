from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_chinatown = 18  # Travel time from Bayview to Chinatown (in minutes)
travel_time_back = 22            # Travel time from Chinatown back to Bayview (in minutes)

# Timing constants
arrival_time = 9 * 60           # Arrival at Bayview at 9:00 AM (540 minutes)
jason_start = 8 * 60 + 30       # Jason will be at Chinatown starting at 8:30 AM (510 minutes)
jason_end = 12 * 60 + 30        # Jason leaves at 12:30 PM (750 minutes)
min_meeting_duration = 90        # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_chinatown)  # Must arrive at Chinatown after travelling
s.add(meeting_start >= jason_start)                               # Meeting must start after Jason is available
s.add(meeting_start + min_meeting_duration <= jason_end)         # Meeting must finish before Jason leaves

# Add a constraint to ensure there is enough time to return after the meeting
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