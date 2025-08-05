from z3 import *
import json

# Define travel times from Richmond to each district
travel_from_richmond = {
    'Bayview': 26,
    'Chinatown': 20,
    'Marina': 9,
    'Financial': 22,
    'Union': 21
}

# Define travel times between districts
travel_time_dict = {
    ('Richmond', 'Marina'): 9,
    ('Richmond', 'Chinatown'): 20,
    ('Richmond', 'Financial'): 22,
    ('Richmond', 'Bayview'): 26,
    ('Richmond', 'Union'): 21,
    ('Marina', 'Richmond'): 11,
    ('Marina', 'Chinatown'): 16,
    ('Marina', 'Financial'): 17,
    ('Marina', 'Bayview'): 27,
    ('Marina', 'Union'): 16,
    ('Chinatown', 'Richmond'): 20,
    ('Chinatown', 'Marina'): 12,
    ('Chinatown', 'Financial'): 5,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'Union'): 7,
    ('Financial', 'Richmond'): 21,
    ('Financial', 'Marina'): 15,
    ('Financial', 'Chinatown'): 5,
    ('Financial', 'Bayview'): 19,
    ('Financial', 'Union'): 9,
    ('Bayview', 'Richmond'): 25,
    ('Bayview', 'Marina'): 25,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'Financial'): 19,
    ('Bayview', 'Union'): 17,
    ('Union', 'Richmond'): 20,
    ('Union', 'Marina'): 18,
    ('Union', 'Chinatown'): 7,
    ('Union', 'Financial'): 9,
    ('Union', 'Bayview'): 15
}

# Meeting details
meetings = [
    {"person": "Margaret", "location": "Bayview", "duration": 30, "avail_start": 30, "avail_end": 270},
    {"person": "Robert", "location": "Chinatown", "duration": 15, "avail_start": 195, "avail_end": 675},
    {"person": "Kimberly", "location": "Marina", "duration": 15, "avail_start": 255, "avail_end": 465},
    {"person": "Rebecca", "location": "Financial", "duration": 75, "avail_start": 255, "avail_end": 465},
    {"person": "Kenneth", "location": "Union", "duration": 75, "avail_start": 630, "avail_end": 735}
]

# Create Z3 solver
s = Solver()

# Create start time variables for each meeting
start_vars = [Int(f'start{i}') for i in range(len(meetings))]

# Add constraints for each meeting
for i, mtg in enumerate(meetings):
    # Start time within availability window
    s.add(start_vars[i] >= mtg['avail_start'])
    s.add(start_vars[i] + mtg['duration'] <= mtg['avail_end'])
    # Start time after travel from Richmond
    s.add(start_vars[i] >= travel_from_richmond[mtg['location']])

# Add disjunctive constraints for every pair of meetings
for i in range(len(meetings)):
    for j in range(i + 1, len(meetings)):
        loc_i = meetings[i]['location']
        loc_j = meetings[j]['location']
        dur_i = meetings[i]['duration']
        dur_j = meetings[j]['duration']
        # Option 1: i before j
        option1 = (start_vars[i] + dur_i + travel_time_dict[(loc_i, loc_j)] <= start_vars[j])
        # Option 2: j before i
        option2 = (start_vars[j] + dur_j + travel_time_dict[(loc_j, loc_i)] <= start_vars[i])
        s.add(Or(option1, option2))

# Check if the schedule is feasible
if s.check() == sat:
    m = s.model()
    # Extract start times
    start_times = [m.evaluate(start_vars[i]).as_long() for i in range(len(meetings))]
    
    # Convert start times to HH:MM format
    def minutes_to_time(total_minutes):
        base_hour = 9
        total_minutes = total_minutes  # from 9:00 AM
        hours = total_minutes // 60
        minutes = total_minutes % 60
        abs_hour = base_hour + hours
        abs_minute = minutes
        return f"{abs_hour:02d}:{abs_minute:02d}"
    
    # Prepare itinerary entries
    itinerary = []
    for i, mtg in enumerate(meetings):
        start_time_str = minutes_to_time(start_times[i])
        end_time = start_times[i] + mtg['duration']
        end_time_str = minutes_to_time(end_time)
        itinerary.append({
            "action": "meet",
            "person": mtg['person'],
            "start_time": start_time_str,
            "end_time": end_time_str
        })
    
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(json.dumps(result, indent=2))
else:
    print("No feasible schedule found.")