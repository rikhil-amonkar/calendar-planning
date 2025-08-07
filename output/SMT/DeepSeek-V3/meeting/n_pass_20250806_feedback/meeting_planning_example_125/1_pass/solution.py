from z3 import *
import datetime

# Travel times in minutes
travel_times = {
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Alamo Square'): 17,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Financial District'): 17,
}

# Convert time strings to minutes since 9:00 AM (540 minutes since midnight)
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Availability and constraints
start_location = 'Embarcadero'
start_time = time_to_minutes('09:00')

stephanie_available_start = time_to_minutes('08:15')
stephanie_available_end = time_to_minutes('11:30')
stephanie_min_duration = 90
stephanie_location = 'Financial District'

john_available_start = time_to_minutes('10:15')
john_available_end = time_to_minutes('20:45')
john_min_duration = 30
john_location = 'Alamo Square'

# Create Z3 variables
stephanie_start = Int('stephanie_start')
stephanie_end = Int('stephanie_end')
john_start = Int('john_start')
john_end = Int('john_end')

s = Solver()

# Constraints for Stephanie
s.add(stephanie_start >= stephanie_available_start)
s.add(stephanie_end <= stephanie_available_end)
s.add(stephanie_end - stephanie_start >= stephanie_min_duration)

# Constraints for John
s.add(john_start >= john_available_start)
s.add(john_end <= john_available_end)
s.add(john_end - john_start >= john_min_duration)

# Travel constraints
# Option 1: Meet Stephanie first, then John
option1_start_to_stephanie = start_time + travel_times[(start_location, stephanie_location)]
option1_stephanie_to_john = stephanie_end + travel_times[(stephanie_location, john_location)]
option1 = And(
    stephanie_start >= option1_start_to_stephanie,
    john_start >= option1_stephanie_to_john
)

# Option 2: Meet John first, then Stephanie
option2_start_to_john = start_time + travel_times[(start_location, john_location)]
option2_john_to_stephanie = john_end + travel_times[(john_location, stephanie_location)]
option2 = And(
    john_start >= option2_start_to_john,
    stephanie_start >= option2_john_to_stephanie
)

# Only one of the options can be true
s.add(Or(option1, option2))

# Maximize the total meeting time
total_meeting_time = (stephanie_end - stephanie_start) + (john_end - john_start)
s.maximize(total_meeting_time)

# Check if a solution exists
if s.check() == sat:
    m = s.model()
    stephanie_start_time = m[stephanie_start].as_long()
    stephanie_end_time = m[stephanie_end].as_long()
    john_start_time = m[john_start].as_long()
    john_end_time = m[john_end].as_long()
    
    itinerary = []
    if stephanie_start_time < john_start_time:
        itinerary.append({
            "action": "meet",
            "person": "Stephanie",
            "start_time": minutes_to_time(stephanie_start_time),
            "end_time": minutes_to_time(stephanie_end_time)
        })
        itinerary.append({
            "action": "meet",
            "person": "John",
            "start_time": minutes_to_time(john_start_time),
            "end_time": minutes_to_time(john_end_time)
        })
    else:
        itinerary.append({
            "action": "meet",
            "person": "John",
            "start_time": minutes_to_time(john_start_time),
            "end_time": minutes_to_time(john_end_time)
        })
        itinerary.append({
            "action": "meet",
            "person": "Stephanie",
            "start_time": minutes_to_time(stephanie_start_time),
            "end_time": minutes_to_time(stephanie_end_time)
        })
    
    print('SOLUTION:')
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")