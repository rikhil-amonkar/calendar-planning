from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_embarcadero = 14  # Travel time from Marina District to Embarcadero (in minutes)
travel_time_back = 12              # Travel time from Embarcadero back to Marina District (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at Marina District at 9:00 AM (540 minutes)
barbara_start = 13 * 60 + 30       # Barbara will be at Embarcadero from 1:30 PM (810 minutes)
barbara_end = 20 * 60 + 45         # Barbara leaves at 8:45 PM (1245 minutes)
min_meeting_duration = 60           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_embarcadero)  # Must arrive at Embarcadero after traveling
s.add(meeting_start >= barbara_start)                              # Meeting must start after Barbara is available
s.add(meeting_start + min_meeting_duration <= barbara_end)        # Meeting must finish before Barbara leaves

# Add a constraint to ensure there is enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")