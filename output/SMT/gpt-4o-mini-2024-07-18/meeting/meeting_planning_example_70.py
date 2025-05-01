from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_north_beach = 24  # Travel time from Golden Gate Park to North Beach (in minutes)
travel_time_back = 22              # Travel time from North Beach back to Golden Gate Park (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at Golden Gate Park at 9:00 AM (540 minutes)
ronald_start = 9 * 60 + 30         # Ronald will be at North Beach from 9:30 AM (570 minutes)
ronald_end = 18 * 60 + 30          # Ronald leaves at 6:30 PM (1110 minutes)
min_meeting_duration = 30           # Minimum meeting duration (in minutes)

# Define variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_north_beach)  # Must arrive at North Beach after travelling
s.add(meeting_start >= ronald_start)                               # Meeting must start after Ronald is available
s.add(meeting_start + min_meeting_duration <= ronald_end)         # Meeting must finish before Ronald leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")