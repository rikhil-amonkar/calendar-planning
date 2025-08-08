from z3 import *
import datetime

def time_to_minutes(time_str):
    hh, mm = map(int, time_str.split(':'))
    return hh * 60 + mm

def minutes_to_time(minutes):
    hh = minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Initialize solver
s = Solver()

# Define variables
# Meeting Stephanie: start and end times in minutes since midnight
steph_start = Int('steph_start')
steph_end = Int('steph_end')
# Meeting John: start and end times in minutes since midnight
john_start = Int('john_start')
john_end = Int('john_end')

# Convert constraints to minutes
embarcadero_arrival = time_to_minutes("09:00")
steph_available_start = time_to_minutes("08:15")
steph_available_end = time_to_minutes("11:30")
john_available_start = time_to_minutes("10:15")
john_available_end = time_to_minutes("20:45")

# Travel times in minutes
travel_emb_to_fin = 5
travel_fin_to_alamo = 17
travel_emb_to_alamo = 19
travel_alamo_to_fin = 17
travel_alamo_to_emb = 17
travel_fin_to_emb = 4

# Constraints for Stephanie's meeting
s.add(steph_start >= steph_available_start)
s.add(steph_end <= steph_available_end)
s.add(steph_end - steph_start >= 90)  # at least 90 minutes

# Constraints for John's meeting
s.add(john_start >= john_available_start)
s.add(john_end <= john_available_end)
s.add(john_end - john_start >= 30)  # at least 30 minutes

# Arrival at Embarcadero at 9:00 AM
# Possible scenarios:
# 1. Go to Financial District first, then Alamo Square
# 2. Go to Alamo Square first, then Financial District

# Scenario 1: Meet Stephanie first, then John
scenario1_possible = And(
    steph_start >= embarcadero_arrival + travel_emb_to_fin,
    john_start >= steph_end + travel_fin_to_alamo
)

# Scenario 2: Meet John first, then Stephanie
scenario2_possible = And(
    john_start >= embarcadero_arrival + travel_emb_to_alamo,
    steph_start >= john_end + travel_alamo_to_fin
)

# At least one scenario must be possible
s.add(Or(scenario1_possible, scenario2_possible))

# Check if the constraints are satisfiable
if s.check() == sat:
    m = s.model()
    steph_start_min = m.eval(steph_start).as_long()
    steph_end_min = m.eval(steph_end).as_long()
    john_start_min = m.eval(john_start).as_long()
    john_end_min = m.eval(john_end).as_long()

    itinerary = []
    # Determine the order based on the scenario that was satisfied
    if m.eval(scenario1_possible):
        # Scenario 1: Stephanie first
        itinerary.append({
            "action": "meet",
            "person": "Stephanie",
            "start_time": minutes_to_time(steph_start_min),
            "end_time": minutes_to_time(steph_end_min)
        })
        itinerary.append({
            "action": "meet",
            "person": "John",
            "start_time": minutes_to_time(john_start_min),
            "end_time": minutes_to_time(john_end_min)
        })
    else:
        # Scenario 2: John first
        itinerary.append({
            "action": "meet",
            "person": "John",
            "start_time": minutes_to_time(john_start_min),
            "end_time": minutes_to_time(john_end_min)
        })
        itinerary.append({
            "action": "meet",
            "person": "Stephanie",
            "start_time": minutes_to_time(steph_start_min),
            "end_time": minutes_to_time(steph_end_min)
        })

    print('SOLUTION:')
    print({"itinerary": itinerary})
else:
    print("No valid schedule found.")