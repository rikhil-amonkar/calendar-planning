from z3 import *

# Create a Z3 solver instance
s = Solver()

# Define constants for the problem
arrival_time = 9 * 60  # Arrival at Bayview at 9:00 AM
travel_time_to_ggp = 22  # Travel time from Bayview to Golden Gate Park in minutes
travel_time_back = 23    # Travel time from Golden Gate Park to Bayview in minutes

# Barbara's availability
barbara_start = 8 * 60  # Barbara is at Golden Gate Park starting at 8:00 AM
barbara_end = 11 * 60 + 30  # Barbara leaves at 11:30 AM
min_meeting_duration = 90  # Minimum meeting duration in minutes

# Define the variable for the meeting start time
meeting_start = Int('meeting_start')

# Constraints for the meeting time
s.add(meeting_start >= arrival_time + travel_time_to_ggp)  # Must arrive at Golden Gate Park after travelling
s.add(meeting_start >= barbara_start)                        # Must arrive after Barbara is available
s.add(meeting_start + min_meeting_duration <= barbara_end)  # Must leave before Barbara is done

# Add a constraint to ensure you have enough time to return after the meeting is over
s.add(meeting_start + min_meeting_duration + travel_time_back <= 24 * 60)  # Must finish before midnight

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    start_time = model[meeting_start].as_long()
    end_time = start_time + min_meeting_duration  # Calculate the end time of the meeting

    print("SOLUTION:")
    print(f"Meeting starts at: {start_time // 60}:{start_time % 60:02d}")
    print(f"Meeting ends at: {end_time // 60}:{end_time % 60:02d}")
else:
    print("No possible trip plan found.")