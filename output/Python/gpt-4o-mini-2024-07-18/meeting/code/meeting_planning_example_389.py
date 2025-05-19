import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Bayview'): 26,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Bayview'): 15,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Mission District'): 13,
}

# Define meeting constraints
constraints = {
    'Sarah': {"location": "Fisherman's Wharf", "available_from": "14:45", "available_to": "17:30", "duration": 105},
    'Mary': {"location": "Richmond District", "available_from": "13:00", "available_to": "19:15", "duration": 75},
    'Helen': {"location": "Mission District", "available_from": "21:45", "available_to": "22:30", "duration": 30},
    'Thomas': {"location": "Bayview", "available_from": "15:15", "available_to": "18:45", "duration": 120},
}

def time_to_minutes(t):
    """Convert time string 'H:MM' to minutes since midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since midnight to time string 'H:MM'."""
    return f"{m // 60}:{m % 60:02}"

def schedule_meetings():
    start_time = "09:00"
    current_time = time_to_minutes(start_time)

    itinerary = []
    meeting_times = {}

    # Meet Mary first if we can
    if current_time <= time_to_minutes(constraints['Mary']['available_to']):
        # Calculate travel time from Haight-Ashbury to Richmond District
        travel_time = travel_times[('Haight-Ashbury', 'Richmond District')]
        arrival_time = current_time + travel_time
        
        if arrival_time < time_to_minutes(constraints['Mary']['available_from']):
            arrival_time = time_to_minutes(constraints['Mary']['available_from'])
        
        end_time = arrival_time + constraints['Mary']['duration']
        
        if end_time <= time_to_minutes(constraints['Mary']['available_to']):
            itinerary.append({
                "action": "meet",
                "location": "Richmond District",
                "person": "Mary",
                "start_time": minutes_to_time(arrival_time),
                "end_time": minutes_to_time(end_time)
            })
            current_time = end_time
            meeting_times['Mary'] = (arrival_time, end_time)

    # Meet Sarah
    if current_time <= time_to_minutes(constraints['Sarah']['available_to']):
        # Calculate travel time from last location (Richmond District) to Fisherman's Wharf
        if 'Mary' in meeting_times:
            travel_time = travel_times[('Richmond District', 'Fisherman\'s Wharf')]
        else:
            travel_time = travel_times[('Haight-Ashbury', 'Fisherman\'s Wharf')]
        
        arrival_time = current_time + travel_time
        
        if arrival_time < time_to_minutes(constraints['Sarah']['available_from']):
            arrival_time = time_to_minutes(constraints['Sarah']['available_from'])
        
        end_time = arrival_time + constraints['Sarah']['duration']
        
        if end_time <= time_to_minutes(constraints['Sarah']['available_to']):
            itinerary.append({
                "action": "meet",
                "location": "Fisherman's Wharf",
                "person": "Sarah",
                "start_time": minutes_to_time(arrival_time),
                "end_time": minutes_to_time(end_time)
            })
            current_time = end_time
            meeting_times['Sarah'] = (arrival_time, end_time)

    # Meet Thomas
    if current_time <= time_to_minutes(constraints['Thomas']['available_to']):
        # Calculate travel time from last location to Bayview
        travel_time = travel_times[('Fisherman\'s Wharf', 'Bayview')] if 'Sarah' in meeting_times else travel_times[('Richmond District', 'Bayview')]
        arrival_time = current_time + travel_time
        
        if arrival_time < time_to_minutes(constraints['Thomas']['available_from']):
            arrival_time = time_to_minutes(constraints['Thomas']['available_from'])
        
        end_time = arrival_time + constraints['Thomas']['duration']
        
        if end_time <= time_to_minutes(constraints['Thomas']['available_to']):
            itinerary.append({
                "action": "meet",
                "location": "Bayview",
                "person": "Thomas",
                "start_time": minutes_to_time(arrival_time),
                "end_time": minutes_to_time(end_time)
            })
            current_time = end_time
            meeting_times['Thomas'] = (arrival_time, end_time)

    # Finally meet Helen
    if current_time <= time_to_minutes(constraints['Helen']['available_to']):
        travel_time = travel_times[('Bayview', 'Mission District')] if 'Thomas' in meeting_times else travel_times[('Fisherman\'s Wharf', 'Mission District')]
        arrival_time = current_time + travel_time
        
        if arrival_time < time_to_minutes(constraints['Helen']['available_from']):
            arrival_time = time_to_minutes(constraints['Helen']['available_from'])
        
        end_time = arrival_time + constraints['Helen']['duration']
        
        if end_time <= time_to_minutes(constraints['Helen']['available_to']):
            itinerary.append({
                "action": "meet",
                "location": "Mission District",
                "person": "Helen",
                "start_time": minutes_to_time(arrival_time),
                "end_time": minutes_to_time(end_time)
            })
            current_time = end_time
            meeting_times['Helen'] = (arrival_time, end_time)

    return {"itinerary": itinerary}

# Run the scheduler and print the result in JSON format
result = schedule_meetings()
print(json.dumps(result, indent=2))