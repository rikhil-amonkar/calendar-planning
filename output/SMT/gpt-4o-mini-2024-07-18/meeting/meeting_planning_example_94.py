from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_russian_hill = 13  # Travel time from Alamo Square to Russian Hill (in minutes)
travel_time_back = 15               # Travel time from Russian Hill back to Alamo Square (in minutes)

# Constants for timing
arrival_time = 9 * 60               # Arrival at Alamo Square at 9:00 AM (540 minutes)
james_start = 11 * 60 + 15          # James will be at Russian Hill starting at 11:15 AM (675 minutes)
james_end = 12 * 60                 # James leaves at 12:00 PM (720 minutes)
min_meeting_duration = 15            # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_russian_hill)  # Must arrive at Russian Hill after traveling
s.add(meeting_start >= james_start)                                   # Meeting must start after James is available
s.add(meeting_start + min_meeting_duration <= james_end)             # Meeting must finish before James leaves

# Ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate when you will finish the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")