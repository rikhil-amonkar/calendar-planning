from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_chinatown = 16  # Travel time from Alamo Square to Chinatown (in minutes)
travel_time_back = 17           # Travel time from Chinatown back to Alamo Square (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at Alamo Square at 9:00 AM (540 minutes)
laura_start = 8 * 60 + 15          # Laura will be at Chinatown from 8:15 AM (495 minutes)
laura_end = 18 * 60 + 45           # Laura leaves at 6:45 PM (1110 minutes)
min_meeting_duration = 15           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_chinatown)  # Must arrive at Chinatown after traveling
s.add(meeting_start >= laura_start)                              # Meeting must start after Laura is available
s.add(meeting_start + min_meeting_duration <= laura_end)        # Meeting must finish before Laura leaves

# Ensure there is enough time to return after the meeting is over
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