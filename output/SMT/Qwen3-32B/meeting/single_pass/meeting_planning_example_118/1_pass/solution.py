from z3 import *
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define arrival times at locations
arrival_union_square = 9 * 60 + 17  # 9:00 AM + 17 min = 9:17 AM
arrival_presidio = 9 * 60 + 31  # 9:31 AM

# Variables for Richard's meeting
richard_start = Int('richard_start')
richard_end = richard_start + 120

# Constraints for Richard: start at arrival_union_square
richard_constraints = [
    richard_start == arrival_union_square,
    richard_end <= 13 * 60  # 1:00 PM
]

# Variables for Charles's meeting
charles_start = Int('charles_start')
charles_end = charles_start + 120

# Charles's earliest start time is max(arrival_presidio, 9:45 AM)
charles_earliest_start = max(arrival_presidio, 9 * 60 + 45)
charles_constraints = [
    charles_start == charles_earliest_start,
    charles_end <= 13 * 60
]

# Check Richard's possibility
solver_richard = Solver()
solver_richard.add(richard_constraints)
if solver_richard.check() == sat:
    model_richard = solver_richard.model()
    start_r = model_richard[richard_start].as_long()
    end_r = start_r + 120
    richard_meeting = {
        "action": "meet",
        "person": "Richard",
        "start_time": minutes_to_time(start_r),
        "end_time": minutes_to_time(end_r)
    }
else:
    richard_meeting = None

# Check Charles's possibility
solver_charles = Solver()
solver_charles.add(charles_constraints)
if solver_charles.check() == sat:
    model_charles = solver_charles.model()
    start_c = model_charles[charles_start].as_long()
    end_c = start_c + 120
    charles_meeting = {
        "action": "meet",
        "person": "Charles",
        "start_time": minutes_to_time(start_c),
        "end_time": minutes_to_time(end_c)
    }
else:
    charles_meeting = None

# Determine which meeting to choose
itinerary = []
if richard_meeting and charles_meeting:
    # Choose the one with earlier start time
    if richard_meeting['start_time'] < charles_meeting['start_time']:
        itinerary.append(richard_meeting)
    else:
        itinerary.append(charles_meeting)
elif richard_meeting:
    itinerary.append(richard_meeting)
elif charles_meeting:
    itinerary.append(charles_meeting)

# Output the JSON
print(json.dumps({"itinerary": itinerary}))