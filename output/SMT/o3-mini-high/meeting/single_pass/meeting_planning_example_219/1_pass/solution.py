from z3 import *
import json

# Convert a time in minutes (since midnight) to a "HH:MM" 24-hour string.
def minutes_to_time(m):
    h = m // 60
    minute = m % 60
    return f"{h:02d}:{minute:02d}"

# Create an optimizer instance
opt = Optimize()

# Define integer variables for meeting start times (minutes since midnight)
E_start = Int('E_start')  # Emily at Alamo Square
B_start = Int('B_start')  # Barbara at Union Square
W_start = Int('W_start')  # William at Chinatown

# Define Boolean variables indicating if we schedule a meeting with each friend
bE = Bool('bE')
bB = Bool('bB')
bW = Bool('bW')

# Constants for meeting durations (in minutes)
E_duration = 105  # Emily
B_duration = 60   # Barbara
W_duration = 105  # William

# Time windows in minutes since midnight:
# 9:00 = 540, 11:45 = 705, 15:15 = 915, 16:45 = 1005, 18:15 = 1095, 
# 17:15 = 1035, 7:00PM = 19:00 = 1140.
E_window_start = 705  # Emily available from 11:45
E_window_end   = 915  # Emily available until 15:15

B_window_start = 1005 # Barbara available from 16:45
B_window_end   = 1095 # Barbara available until 18:15

W_window_start = 1035 # William available from 17:15
W_window_end   = 1140 # William available until 19:00

# Add constraints for each meeting if it is selected.
# For Emily at Alamo Square:
opt.add(Implies(bE, E_start >= E_window_start))
opt.add(Implies(bE, E_start + E_duration <= E_window_end))

# For Barbara at Union Square:
opt.add(Implies(bB, B_start >= B_window_start))
opt.add(Implies(bB, B_start + B_duration <= B_window_end))

# For William at Chinatown:
opt.add(Implies(bW, W_start >= W_window_start))
opt.add(Implies(bW, W_start + W_duration <= W_window_end))
# With William's window length exactly equal to 105 minutes,
# the only feasible assignment (if chosen) is W_start == 1035.
opt.add(Implies(bW, W_start == W_window_start))

# Travel times (in minutes) between locations:
# From starting point The Castro (where you arrive at 9:00 = 540)
# to:
# Alamo Square: 8
# Union Square: 19
# Chinatown: 20
#
# And between these friend venues:
# Castro -> Alamo: 8, Castro -> Union: 19, Castro -> Chinatown: 20.
# Alamo -> Union: 14, Alamo -> Chinatown: 16.
# Union -> Chinatown: 7.
# (The reverse directions are given but since we only travel forward in time 
# after meeting, we only need the travel times between the consecutive meetings.)

# If you meet Emily then Barbara, you must have enough travel time from Alamo Square to Union Square.
# (Travel time from Alamo Square to Union Square is 14 minutes.)
opt.add(Implies(And(bE, bB), B_start >= E_start + E_duration + 14))

# If you meet Emily then William, you must allow travel from Alamo Square to Chinatown.
# (Travel time from Alamo Square to Chinatown is 16 minutes.)
opt.add(Implies(And(bE, bW), W_start >= E_start + E_duration + 16))

# If you meet Barbara then William, you must allow travel from Union Square to Chinatown.
# (Travel time from Union Square to Chinatown is 7 minutes.)
opt.add(Implies(And(bB, bW), W_start >= B_start + B_duration + 7))

# It turns out that the windows for Barbara (16:45-18:15 for a 60-min meeting)
# and William (17:15-19:00 for a 105-min meeting) are mutually incompatible if done sequentially.
# So we explicitly disallow scheduling both:
opt.add(Or(Not(bB), Not(bW)))  # At most one of Barbara and William can be scheduled.

# (The initial travel from The Castro at 9:00 is automatically satisfied because
# all friend windows start well after 9:00 + travel time.)

# Define objectives. Our primary goal is to maximize the number of friends met,
# and as a secondary objective, maximize the total meeting time.
count = If(bE, 1, 0) + If(bB, 1, 0) + If(bW, 1, 0)
meeting_total = E_duration * If(bE, 1, 0) + B_duration * If(bB, 1, 0) + W_duration * If(bW, 1, 0)

opt.maximize(count)
opt.maximize(meeting_total)

# (Optionally, we could constrain bE = True because Emily's meeting window is far ahead of the others,
# but we let the optimizer choose.)
# We also know that starting at The Castro at 9:00 doesn't restrict the later meetings.

# Check and get the model
if opt.check() == sat:
    model = opt.model()
    
    itinerary = []
    
    # Create a list of meetings if scheduled, with their computed start and end times.
    if is_true(model.eval(bE)):
        start = model.eval(E_start).as_long()
        end = start + E_duration
        itinerary.append({
            "action": "meet",
            "person": "Emily",
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    
    if is_true(model.eval(bB)):
        start = model.eval(B_start).as_long()
        end = start + B_duration
        itinerary.append({
            "action": "meet",
            "person": "Barbara",
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    
    if is_true(model.eval(bW)):
        start = model.eval(W_start).as_long()
        end = start + W_duration
        itinerary.append({
            "action": "meet",
            "person": "William",
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
    
    # Sort itinerary by start time to ensure chronological order
    itinerary.sort(key=lambda x: x["start_time"])
    
    # Output the result as JSON.
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found.")