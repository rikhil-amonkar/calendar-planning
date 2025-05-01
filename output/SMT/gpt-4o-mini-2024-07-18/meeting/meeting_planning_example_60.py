from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_chinatown = 7  # Travel time from Union Square to Chinatown (in minutes)
travel_time_back = 7           # Travel time from Chinatown back to Union Square (in minutes)

# Constants for timing
arrival_time = 9 * 60          # Arrival at Union Square at 9:00 AM (540 minutes)
carol_start = 18 * 60 + 30     # Carol is at Chinatown from 6:30 PM (1110 minutes)
carol_end = 20 * 60            # Carol leaves at 8:00 PM (1200 minutes)
min_meeting_duration = 45       # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_chinatown)  # Must arrive at Chinatown after traveling
s.add(meeting_start >= carol_start)                              # Meeting must start after Carol arrives
s.add(meeting_start + min_meeting_duration <= carol_end)        # Meeting must finish before Carol leaves

# Ensure sufficient time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate meeting end time

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format to HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format to HH:MM
else:
    print("No possible trip plan found.")