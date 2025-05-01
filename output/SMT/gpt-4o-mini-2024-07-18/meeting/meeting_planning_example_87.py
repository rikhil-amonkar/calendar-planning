from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_pacific_heights = 11  # Travel time from Embarcadero to Pacific Heights (in minutes)
travel_time_back = 10                  # Travel time from Pacific Heights back to Embarcadero (in minutes)

# Constants for timing
arrival_time = 9 * 60                 # Arrival at Embarcadero at 9:00 AM (540 minutes)
james_start = 8 * 60 + 30             # James will be at Pacific Heights from 8:30 AM (510 minutes)
james_end = 15 * 60                   # James leaves at 3:00 PM (900 minutes)
min_meeting_duration = 75              # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_pacific_heights)  # Must arrive at Pacific Heights after traveling
s.add(meeting_start >= james_start)                                     # Meeting must start after James is available
s.add(meeting_start + min_meeting_duration <= james_end)               # Meeting must finish before James leaves

# Ensure there's enough time to return back after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate the end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")  # Format time as HH:MM
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")      # Format time as HH:MM
else:
    print("No possible trip plan found.")