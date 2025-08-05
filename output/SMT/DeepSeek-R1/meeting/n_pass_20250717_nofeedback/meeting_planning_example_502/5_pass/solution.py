from z3 import *

# Generate time slots from 09:00 to 17:45 in 15-minute intervals
time_slots = []
hour = 9
minute = 0
for i in range(33):
    time_slots.append(f"{hour:02d}:{minute:02d}")
    minute += 15
    if minute >= 60:
        minute = 0
        hour += 1

# Create solver and variables
s = Solver()
rebecca_start = Int('rebecca_start')
stephanie_start = Int('stephanie_start')
brian_start = Int('brian_start')
steven_start = Int('steven_start')

# Set variable domains
s.add(rebecca_start >= 0, rebecca_start <= 10)
s.add(stephanie_start >= 0, stephanie_start <= 5)
s.add(brian_start >= 14, brian_start <= 22)
s.add(steven_start >= brian_start + 2, steven_start <= 25)

# Ensure Rebecca and Stephanie meetings do not overlap
s.add(Or(
    rebecca_start + 2 <= stephanie_start,
    stephanie_start + 7 <= rebecca_start
))

# Check for a valid solution
if s.check() == sat:
    m = s.model()
    r = m[rebecca_start].as_long()
    st = m[stephanie_start].as_long()
    b = m[brian_start].as_long()
    sv = m[steven_start].as_long()
    
    itinerary = [
        {'action': 'meet', 'person': 'Rebecca', 'start_time': time_slots[r], 'end_time': time_slots[r+2]},
        {'action': 'meet', 'person': 'Stephanie', 'start_time': time_slots[st], 'end_time': time_slots[st+7]},
        {'action': 'meet', 'person': 'Karen', 'start_time': time_slots[13], 'end_time': time_slots[14]},
        {'action': 'meet', 'person': 'Brian', 'start_time': time_slots[b], 'end_time': time_slots[b+2]},
        {'action': 'meet', 'person': 'Steven', 'start_time': time_slots[sv], 'end_time': time_slots[sv+8]}
    ]
    print(f"Plan found: {itinerary}")
else:
    print("No valid plan found")