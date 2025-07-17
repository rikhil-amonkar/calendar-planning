from z3 import *
import datetime

# Define the travel times between districts
travel_times = {
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Marina District'): 9,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Marina District'): 6,
    ('Marina District', 'Richmond District'): 11,  # Note: Typo in original data (Richmond vs Richmond)
    ('Marina District', 'Pacific Heights'): 7,
}

# Correct the typo in the travel times dictionary
travel_times[('Marina District', 'Richmond District')] = 11

# Friend availability
carol_available_start = datetime.datetime.strptime("11:30", "%H:%M")
carol_available_end = datetime.datetime.strptime("15:00", "%H:%M")
carol_min_duration = 60  # minutes

jessica_available_start = datetime.datetime.strptime("15:30", "%H:%M")
jessica_available_end = datetime.datetime.strptime("16:45", "%H:%M")
jessica_min_duration = 45  # minutes

# Create Z3 variables
s = Solver()

# Meeting start times (in minutes since 9:00 AM)
carol_meet_start = Int('carol_meet_start')
carol_meet_end = Int('carol_meet_end')
jessica_meet_start = Int('jessica_meet_start')
jessica_meet_end = Int('jessica_meet_end')

# Current location starts at Richmond District at 9:00 AM (0 minutes)
current_location = 'Richmond District'

# Constraints for Carol meeting
s.add(carol_meet_start >= (carol_available_start - datetime.datetime.strptime("9:00", "%H:%M")).total_seconds() / 60)
s.add(carol_meet_end <= (carol_available_end - datetime.datetime.strptime("9:00", "%H:%M")).total_seconds() / 60)
s.add(carol_meet_end - carol_meet_start >= carol_min_duration)

# Travel to Carol (from Richmond to Marina)
s.add(carol_meet_start >= travel_times[(current_location, 'Marina District')])

# Constraints for Jessica meeting
s.add(jessica_meet_start >= (jessica_available_start - datetime.datetime.strptime("9:00", "%H:%M")).total_seconds() / 60)
s.add(jessica_meet_end <= (jessica_available_end - datetime.datetime.strptime("9:00", "%H:%M")).total_seconds() / 60)
s.add(jessica_meet_end - jessica_meet_start >= jessica_min_duration)

# Travel between meetings
# Option 1: Carol first, then Jessica
option1 = And(
    jessica_meet_start >= carol_meet_end + travel_times[('Marina District', 'Pacific Heights')]
)

# Option 2: Jessica first, then Carol (but this isn't possible due to time constraints)
option2 = And(
    carol_meet_start >= jessica_meet_end + travel_times[('Pacific Heights', 'Marina District')]
)

# We'll try option1 first since option2 is likely impossible
s.add(option1)

# Maximize the total meeting time
total_meeting_time = (carol_meet_end - carol_meet_start) + (jessica_meet_end - jessica_meet_start)
optimize = Optimize()
optimize.add(s.assertions())
optimize.maximize(total_meeting_time)

if optimize.check() == sat:
    model = optimize.model()
    carol_start = model[carol_meet_start].as_long()
    carol_end = model[carol_meet_end].as_long()
    jessica_start = model[jessica_meet_start].as_long()
    jessica_end = model[jessica_meet_end].as_long()
    
    # Convert minutes since 9:00 AM to HH:MM format
    def minutes_to_time(minutes):
        base = datetime.datetime.strptime("9:00", "%H:%M")
        delta = datetime.timedelta(minutes=minutes)
        return (base + delta).strftime("%H:%M")
    
    itinerary = [
        {"action": "meet", "person": "Carol", "start_time": minutes_to_time(carol_start), "end_time": minutes_to_time(carol_end)},
        {"action": "meet", "person": "Jessica", "start_time": minutes_to_time(jessica_start), "end_time": minutes_to_time(jessica_end)}
    ]
    
    print('{"itinerary": ' + str(itinerary).replace("'", '"') + '}')
else:
    print('{"itinerary": []}')