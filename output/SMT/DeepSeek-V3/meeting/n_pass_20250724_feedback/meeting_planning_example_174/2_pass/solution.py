from z3 import *
import datetime
import json

# Define travel times between locations
travel_times = {
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Mission District'): 13,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Pacific Heights'): 16
}

# Define friend availability
friends = {
    'Thomas': {
        'location': 'Pacific Heights',
        'start': datetime.time(15, 30),  # 3:30 PM
        'end': datetime.time(19, 15),    # 7:15 PM
        'duration': 75                   # minutes
    },
    'Kenneth': {
        'location': 'Mission District',
        'start': datetime.time(12, 0),   # 12:00 PM
        'end': datetime.time(15, 45),    # 3:45 PM
        'duration': 45                   # minutes
    }
}

# Current location and time
current_location = 'Nob Hill'
current_time = datetime.datetime.combine(datetime.date.today(), datetime.time(9, 0))  # 9:00 AM

# Create Z3 variables and solver
s = Solver()

# Variables for meeting start times (in minutes since 9:00 AM)
thomas_start = Int('thomas_start')
kenneth_start = Int('kenneth_start')

# Convert friend availability to minutes since 9:00 AM
thomas_available_start = (15 * 60 + 30) - (9 * 60)  # 3:30 PM is 390 minutes after 9:00 AM
thomas_available_end = (19 * 60 + 15) - (9 * 60)    # 7:15 PM is 495 minutes after 9:00 AM
kenneth_available_start = (12 * 60) - (9 * 60)      # 12:00 PM is 180 minutes after 9:00 AM
kenneth_available_end = (15 * 60 + 45) - (9 * 60)    # 3:45 PM is 405 minutes after 9:00 AM

# Constraints for meeting times within availability
s.add(thomas_start >= thomas_available_start)
s.add(thomas_start + 75 <= thomas_available_end)
s.add(kenneth_start >= kenneth_available_start)
s.add(kenneth_start + 45 <= kenneth_available_end)

# Variables to track which meeting comes first
meet_thomas_first = Bool('meet_thomas_first')

# Constraints for travel times
# Option 1: Meet Kenneth first, then Thomas
s.add(Implies(Not(meet_thomas_first),
    And(
        kenneth_start >= travel_times[(current_location, 'Mission District')],
        thomas_start >= kenneth_start + 45 + travel_times[('Mission District', 'Pacific Heights')]
    )
))

# Option 2: Meet Thomas first, then Kenneth
s.add(Implies(meet_thomas_first,
    And(
        thomas_start >= travel_times[(current_location, 'Pacific Heights')],
        kenneth_start >= thomas_start + 75 + travel_times[('Pacific Heights', 'Mission District')]
    )
))

# We want to maximize the number of friends met (both in this case)
# Check if both meetings can be scheduled
if s.check() == sat:
    model = s.model()
    
    # Determine which meeting comes first
    if is_true(model[meet_thomas_first]):
        # Thomas first
        thomas_start_min = model[thomas_start].as_long()
        kenneth_start_min = model[kenneth_start].as_long()
    else:
        # Kenneth first
        kenneth_start_min = model[kenneth_start].as_long()
        thomas_start_min = model[thomas_start].as_long()
    
    # Convert minutes back to time strings
    def minutes_to_time(minutes):
        dt = current_time + datetime.timedelta(minutes=minutes)
        return dt.strftime("%H:%M")
    
    itinerary = []
    
    # Add meetings to itinerary in chronological order
    if is_true(model[meet_thomas_first]):
        itinerary.append({
            "action": "meet",
            "person": "Thomas",
            "start_time": minutes_to_time(thomas_start_min),
            "end_time": minutes_to_time(thomas_start_min + 75)
        })
        itinerary.append({
            "action": "meet",
            "person": "Kenneth",
            "start_time": minutes_to_time(kenneth_start_min),
            "end_time": minutes_to_time(kenneth_start_min + 45)
        })
    else:
        itinerary.append({
            "action": "meet",
            "person": "Kenneth",
            "start_time": minutes_to_time(kenneth_start_min),
            "end_time": minutes_to_time(kenneth_start_min + 45)
        })
        itinerary.append({
            "action": "meet",
            "person": "Thomas",
            "start_time": minutes_to_time(thomas_start_min),
            "end_time": minutes_to_time(thomas_start_min + 75)
        })
    
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"itinerary": []}, indent=2))