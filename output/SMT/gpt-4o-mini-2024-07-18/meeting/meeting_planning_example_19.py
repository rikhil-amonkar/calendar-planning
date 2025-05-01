from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define travel times
travel_time_to_pacific_heights = 16  # Travel time from Golden Gate Park to Pacific Heights (in minutes)
travel_time_back = 15                  # Travel time from Pacific Heights back to Golden Gate Park (in minutes)

# Constants for timing
arrival_time = 9 * 60  # Arrival at Golden Gate Park at 9:00 AM (540 minutes)
john_start = 19 * 60 + 45  # John is available at Pacific Heights starting at 7:45 PM (1185 minutes)
john_end = 20 * 60 + 45    # John leaves at 8:45 PM (1245 minutes)
min_meeting_duration = 45   # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_pacific_heights)  # Must arrive after traveling
s.add(meeting_start >= john_start)                                      # Must meet after John is available
s.add(meeting_start + min_meeting_duration <= john_end)                # Must finish before John leaves

# Add a constraint to ensure you can return after the meeting
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate meeting end time

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")