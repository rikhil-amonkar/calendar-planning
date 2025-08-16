import z3
import json

# Initialize the solver
s = z3.Solver()

# Define variables for start times of each meeting
S_John = z3.Int('S_John')
S_Steven = z3.Int('S_Steven')
S_Barbara = z3.Int('S_Barbara')

# Constraints for John (Pacific Heights)
# Arrive at Pacific Heights from Nob Hill at 9:00 AM + 8 minutes = 9:08 AM (548 minutes)
s.add(S_John >= 9 * 60 + 8)  # 9:08 AM
# John's meeting must end before 1:30 PM (810 minutes)
s.add(S_John + 15 <= 810)

# Constraints for Steven (North Beach)
# Travel time from Pacific Heights to North Beach is 9 minutes
s.add(S_Steven >= S_John + 15 + 9)
# Steven is available from 1:30 PM (810 minutes)
s.add(S_Steven >= 810)
# Steven's meeting must end before 10:00 PM (22:00 = 1320 minutes)
s.add(S_Steven + 45 <= 1320)

# Constraints for Barbara (Fisherman's Wharf)
# Travel time from North Beach to Fisherman's Wharf is 6 minutes
s.add(S_Barbara >= S_Steven + 45 + 6)
# Barbara is available from 6:00 PM (1080 minutes)
s.add(S_Barbara >= 1080)
# Barbara's meeting must end before 9:30 PM (21:30 = 1290 minutes)
s.add(S_Barbara + 30 <= 1290)

# Check for a solution
if s.check() == z3.sat:
    model = s.model()
    
    # Extract the meeting times
    john_start = model[S_John].as_long()
    john_end = john_start + 15
    steven_start = model[S_Steven].as_long()
    steven_end = steven_start + 45
    barbara_start = model[S_Barbara].as_long()
    barbara_end = barbara_start + 30

    # Convert minutes to HH:MM format
    def to_time(mins):
        hours = mins // 60
        minutes = mins % 60
        return f"{hours:02d}:{minutes:02d}"

    # Build the itinerary
    itinerary = [
        {"action": "meet", "person": "John", "start_time": to_time(john_start), "end_time": to_time(john_end)},
        {"action": "meet", "person": "Steven", "start_time": to_time(steven_start), "end_time": to_time(steven_end)},
        {"action": "meet", "person": "Barbara", "start_time": to_time(barbara_start), "end_time": to_time(barbara_end)}
    ]

    # Output the solution
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No feasible solution found.")