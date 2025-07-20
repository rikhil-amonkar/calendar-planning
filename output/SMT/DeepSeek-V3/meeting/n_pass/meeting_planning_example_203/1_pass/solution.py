from z3 import *
import datetime
import json

def time_to_minutes(time_str):
    hh, mm = map(int, time_str.split(':'))
    return hh * 60 + mm

def minutes_to_time(minutes):
    hh = minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Travel times in minutes (from -> to)
travel_times = {
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Pacific Heights'): 16,
}

# Friends' availability and constraints
friends = {
    'David': {
        'location': 'Fisherman\'s Wharf',
        'available_start': '10:45',
        'available_end': '15:30',
        'min_duration': 15,
    },
    'Timothy': {
        'location': 'Pacific Heights',
        'available_start': '09:00',
        'available_end': '15:30',
        'min_duration': 75,
    },
    'Robert': {
        'location': 'Mission District',
        'available_start': '12:15',
        'available_end': '19:45',
        'min_duration': 90,
    }
}

# Initialize Z3 solver
s = Solver()

# Create variables for each meeting's start and end times (in minutes since 9:00)
start_vars = {}
end_vars = {}
for name in friends:
    start_vars[name] = Int(f'start_{name}')
    end_vars[name] = Int(f'end_{name}')

# Current location starts at Financial District at 9:00 (0 minutes)
current_location = 'Financial District'

# Constraints for each friend
for name in friends:
    friend = friends[name]
    available_start = time_to_minutes(friend['available_start']) - time_to_minutes('09:00')
    available_end = time_to_minutes(friend['available_end']) - time_to_minutes('09:00')
    min_duration = friend['min_duration']
    
    # Meeting must start within availability window
    s.add(start_vars[name] >= available_start)
    s.add(end_vars[name] <= available_end)
    # Meeting duration must be at least min_duration
    s.add(end_vars[name] - start_vars[name] >= min_duration)
    # Start time must be before end time
    s.add(start_vars[name] < end_vars[name])

# Constraints for traveling between meetings
# Order: Timothy (Pacific Heights) -> David (Fisherman's Wharf) -> Robert (Mission District)
s.add(start_vars['Timothy'] >= travel_times[(current_location, friends['Timothy']['location'])])
s.add(start_vars['David'] >= end_vars['Timothy'] + travel_times[(friends['Timothy']['location'], friends['David']['location'])])
s.add(start_vars['Robert'] >= end_vars['David'] + travel_times[(friends['David']['location'], friends['Robert']['location'])])

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    itinerary = []
    
    # Collect all meetings
    for name in friends:
        start_min = model.evaluate(start_vars[name]).as_long()
        end_min = model.evaluate(end_vars[name]).as_long()
        
        # Convert minutes since 9:00 to HH:MM
        start_time = (datetime.datetime(2023, 1, 1, 9, 0) + datetime.timedelta(minutes=start_min)).strftime('%H:%M')
        end_time = (datetime.datetime(2023, 1, 1, 9, 0) + datetime.timedelta(minutes=end_min)).strftime('%H:%M')
        
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": start_time,
            "end_time": end_time
        })
    
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    
    print('SOLUTION:')
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No feasible schedule found.")