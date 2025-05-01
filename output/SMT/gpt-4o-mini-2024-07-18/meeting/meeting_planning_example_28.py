from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times and timing
travel_time_to_chinatown = 7  # Travel time from Union Square to Chinatown (in minutes)
travel_time_back = 7           # Travel time from Chinatown back to Union Square (in minutes)

# Constants for timing
arrival_time = 9 * 60         # Arrival at Union Square at 9:00 AM (in minutes)
joshua_start = 18 * 60        # Joshua is at Chinatown starting at 6:00 PM (1080 minutes)
joshua_end = 21 * 60 + 30     # Joshua leaves at 9:30 PM (1290 minutes)
min_meeting_duration = 75      # Minimum meeting duration in minutes

# Define variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_chinatown)  # Must arrive at Chinatown after traveling
s.add(meeting_start >= joshua_start)                             # Meeting must start after Joshua is available
s.add(meeting_start + min_meeting_duration <= joshua_end)       # Meeting must finish before Joshua leaves

# Ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate end time of meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")