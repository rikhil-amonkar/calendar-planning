from z3 import Optimize, Int, sat
import json

# Helper function to convert minutes to H:MM 24-hour string format
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Define time constants in minutes (from midnight)
ARRIVAL_ALAMO = 9 * 60       # 9:00 AM -> 540 minutes
TIMOTHY_AVAILABLE_START = 20 * 60 + 45  # 20:45 -> 1245 minutes
TIMOTHY_AVAILABLE_END   = 21 * 60 + 30   # 21:30 -> 1290 minutes

# Travel times in minutes
TRAVEL_ALAMO_TO_RICHMOND = 12
# (Richmond District to Alamo Square travel time is 13, but not needed here)

# Create an Optimize object
opt = Optimize()

# Decision variables:
# d: departure time from Alamo Square to travel to Richmond District
d = Int('departure_time')
# For the meeting at Alamo Square with a local friend (we call her Alice)
# Meeting start is fixed at ARRIVAL_ALAMO and ends at time a_end (which is effectively d)
a_end = Int('alice_meeting_end')

# For the meeting with Timothy at Richmond District:
t_start = Int('timothy_meeting_start')
t_end = Int('timothy_meeting_end')

# Add constraints:
# You arrive at Alamo Square at 9:00, so any meeting there starts at 9:00.
# Alice's meeting goes from 9:00 to the departure time d.
opt.add(d >= ARRIVAL_ALAMO)   # Can only leave after arriving
opt.add(a_end == d)           # Alice meeting ends exactly when you depart

# The travel constraint: after leaving, it takes TRAVEL_ALAMO_TO_RICHMOND minutes to get to Richmond.
# So you must arrive in time for Timothy's meeting.
opt.add(d + TRAVEL_ALAMO_TO_RICHMOND <= t_start)

# Timothy's availability constraints and minimum meeting duration of 45 minutes:
opt.add(t_start >= TIMOTHY_AVAILABLE_START)
opt.add(t_end <= TIMOTHY_AVAILABLE_END)
opt.add(t_end - t_start >= 45)

# To maximize your day meeting friends, you want to delay your departure as much as possible,
# so that the meeting with Alice at Alamo Square lasts longer; however, you must still make it in time.
# Since Timothy is only available until 21:30, and his meeting must last at least 45 minutes,
# the best is to schedule his meeting to exactly span from 20:45 to 21:30.
opt.add(t_start <= TIMOTHY_AVAILABLE_START)  # forces t_start == TIMOTHY_AVAILABLE_START
# Similarly, t_end must then be exactly 21:30:
opt.add(t_end == TIMOTHY_AVAILABLE_END)

# With t_start fixed at 1245, the travel constraint gives: d <= 1245 - 12 = 1233.
opt.add(d <= TIMOTHY_AVAILABLE_START - TRAVEL_ALAMO_TO_RICHMOND)

# Objective: maximize d (i.e. delay departure as late as possible so that you can meet your Alamo friend longer)
h = opt.maximize(d)

# Check for satisfiability and get the optimal model
if opt.check() == sat:
    model = opt.model()
    departure_time = model[d].as_long()
    alice_meeting_end = model[a_end].as_long()  # should equal departure_time
    timothy_meeting_start = model[t_start].as_long()
    timothy_meeting_end = model[t_end].as_long()

    # Build the itinerary with two meeting events:
    # 1. Meeting with Alice at Alamo Square from arrival until departure.
    # 2. Meeting with Timothy at Richmond District once you arrive.
    itinerary = [
        {
            "action": "meet",
            "location": "Alamo Square",
            "person": "Alice",
            "start_time": minutes_to_time(ARRIVAL_ALAMO),
            "end_time": minutes_to_time(alice_meeting_end)
        },
        {
            "action": "meet",
            "location": "Richmond District",
            "person": "Timothy",
            "start_time": minutes_to_time(timothy_meeting_start),
            "end_time": minutes_to_time(timothy_meeting_end)
        }
    ]

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))