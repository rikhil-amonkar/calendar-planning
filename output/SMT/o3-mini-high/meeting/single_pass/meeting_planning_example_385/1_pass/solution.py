from z3 import *

# Convert a time in minutes-since-midnight to "HH:MM" string
def minutes_to_hhmm(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# -------------------------------
# Data and settings
# -------------------------------
# Our starting location is Nob Hill at 09:00 (540 minutes).
# Friends:
#   Jeffrey: at Presidio from 08:00 (480) to 10:00 (600), meeting >= 105 minutes.
#   Steven: at North Beach from 13:30 (810) to 22:00 (1320), meeting >= 45 minutes.
#   Barbara: at Fisherman's Wharf from 18:00 (1080) to 21:30 (1290), meeting >= 30 minutes.
#   John: at Pacific Heights from 09:00 (540) to 13:30 (810), meeting >= 15 minutes.
#
# Travel times (in minutes) between locations are given.
# In our chosen schedule we will meet:
#   John first (at Pacific Heights),
#   then Steven (at North Beach),
#   then Barbara (at Fisherman's Wharf).
#
# Note: Trying to meet Jeffrey is infeasible because from Nob Hill
# (our start at 09:00) the earliest we can arrive at Presidio is 09:17,
# and with a 105-minute meeting we would finish after 10:00.

# Travel time lookup (only those we need for our chosen order):
travel = {
    ("Nob Hill", "Pacific Heights"): 8,         # initial leg to John
    ("Pacific Heights", "North Beach"): 9,        # John -> Steven
    ("North Beach", "Fisherman's Wharf"): 5       # Steven -> Barbara
}

# -------------------------------
# Create Z3 solver and variables
# -------------------------------
s = Solver()

# We'll create integer variables representing meeting start times (in minutes since midnight)
# for John, Steven, and Barbara. We will set the meeting durations to their minimum required times.
John_start = Int('John_start')
John_end   = Int('John_end')
Steven_start = Int('Steven_start')
Steven_end   = Int('Steven_end')
Barbara_start = Int('Barbara_start')
Barbara_end   = Int('Barbara_end')

# Set the meeting durations exactly equal to the minimum requirements (for earliest finish times)
s.add(John_end == John_start + 15)    # John meeting at Pacific Heights must be at least 15 minutes.
s.add(Steven_end == Steven_start + 45)  # Steven meeting at North Beach must be at least 45 minutes.
s.add(Barbara_end == Barbara_start + 30)  # Barbara meeting at Fisherman's Wharf must be at least 30 minutes.

# -------------------------------
# Add constraints for availability and travel times.
# -------------------------------

# Starting constraint: We begin at Nob Hill at 09:00 (540 minutes).
# For John (at Pacific Heights) we must account for travel time from Nob Hill.
s.add(John_start >= 540 + travel[("Nob Hill", "Pacific Heights")])  # >= 540+8 = 548.
# John's availability: 09:00 (540) to 13:30 (810)
s.add(John_start >= 540)        # redundant given travel constraint but added for clarity.
s.add(John_end <= 810)          # must finish by 13:30.

# For Steven (at North Beach):
# Steven is available from 13:30 (810) to 22:00 (1320).
s.add(Steven_start >= 810)
s.add(Steven_end <= 1320)
# Also, we must leave John and travel from Pacific Heights to North Beach.
s.add(Steven_start >= John_end + travel[("Pacific Heights", "North Beach")])  # John_end + 9

# For Barbara (at Fisherman's Wharf):
# Barbara is available from 18:00 (1080) to 21:30 (1290).
s.add(Barbara_start >= 1080)
s.add(Barbara_end <= 1290)
# Must travel from North Beach to Fisherman's Wharf after meeting Steven.
s.add(Barbara_start >= Steven_end + travel[("North Beach", "Fisherman's Wharf")])  # Steven_end + 5

# -------------------------------
# Check solvability and extract a model.
# -------------------------------
if s.check() == sat:
    m = s.model()
    john_s = m[John_start].as_long()
    john_e = m[John_end].as_long()
    steven_s = m[Steven_start].as_long()
    steven_e = m[Steven_end].as_long()
    barbara_s = m[Barbara_start].as_long()
    barbara_e = m[Barbara_end].as_long()

    # Build the itinerary list according to the required JSON format.
    itinerary = [
        {"action": "meet", "person": "John", "start_time": minutes_to_hhmm(john_s), "end_time": minutes_to_hhmm(john_e)},
        {"action": "meet", "person": "Steven", "start_time": minutes_to_hhmm(steven_s), "end_time": minutes_to_hhmm(steven_e)},
        {"action": "meet", "person": "Barbara", "start_time": minutes_to_hhmm(barbara_s), "end_time": minutes_to_hhmm(barbara_e)},
    ]

    # Print the JSON-formatted dictionary.
    result = {"itinerary": itinerary}
    print(result)
else:
    print("No solution found")