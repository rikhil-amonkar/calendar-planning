from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for travel times
travel_time_to_golden_gate = 11  # Travel time from Sunset District to Golden Gate Park (in minutes)
travel_time_back = 10              # Travel time from Golden Gate Park back to Sunset District (in minutes)

# Constants for timing
arrival_time = 9 * 60              # Arrival at Sunset District at 9:00 AM (540 minutes)
joshua_start = 20 * 60 + 45        # Joshua will be at Golden Gate Park from 8:45 PM (1245 minutes)
joshua_end = 21 * 60 + 45          # Joshua leaves at 9:45 PM (1290 minutes)
min_meeting_duration = 15           # Minimum meeting duration (in minutes)

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for meeting time
s.add(meeting_start >= arrival_time + travel_time_to_golden_gate)  # Must arrive at Golden Gate Park after traveling
s.add(meeting_start >= joshua_start)                               # Meeting must start after Joshua is available
s.add(meeting_start + min_meeting_duration <= joshua_end)         # Meeting must finish before Joshua leaves

# Ensure there's enough time to return after the meeting
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