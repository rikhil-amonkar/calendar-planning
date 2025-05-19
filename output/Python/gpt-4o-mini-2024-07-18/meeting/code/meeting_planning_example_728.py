import json
from datetime import datetime, timedelta

# Travel times in minutes
travel_times = {
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Russian Hill'): 8,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Russian Hill'): 15,
    ('Fisherman\'s Wharf', 'Presidio'): 19,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Financial District'): 23,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Russian Hill'): 13,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Russian Hill'): 24,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Russian Hill'): 11,
    ('Haight-Ashbury', 'Russian Hill'): 17,
}

# Meeting constraints
constraints = {
    "Karen": {"location": "Mission District", "start": "14:15", "end": "22:00", "duration": 30},
    "Richard": {"location": "Fisherman's Wharf", "start": "14:30", "end": "17:30", "duration": 30},
    "Robert": {"location": "Presidio", "start": "21:45", "end": "22:45", "duration": 60},
    "Joseph": {"location": "Union Square", "start": "11:45", "end": "14:45", "duration": 120},
    "Helen": {"location": "Sunset District", "start": "14:45", "end": "20:45", "duration": 105},
    "Elizabeth": {"location": "Financial District", "start": "10:00", "end": "12:45", "duration": 75},
    "Kimberly": {"location": "Haight-Ashbury", "start": "14:15", "end": "17:30", "duration": 105},
    "Ashley": {"location": "Russian Hill", "start": "11:30", "end": "21:30", "duration": 45},
}

# Start time
arrival_time = datetime.strptime("09:00", "%H:%M")

# Schedule itinerary
itinerary = []

# Meet Elizabeth first since her time constraint is the tightest
def add_meeting(person, duration, location, start, end):
    start_time = max(start, arrival_time + timedelta(minutes=travel_times.get(('Marina District', location), 0)))
    end_time = start_time + timedelta(minutes=duration)
    
    if end_time <= end:
        itinerary.append({"action": "meet", "location": location, "person": person, 
                          "start_time": start_time.strftime("%H:%M"), 
                          "end_time": end_time.strftime("%H:%M")})
        return end_time
    return None

# Meeting with Elizabeth
elizabeth_start = datetime.strptime("10:00", "%H:%M")
elizabeth_end = datetime.strptime("12:45", "%H:%M")
arrival_time = add_meeting("Elizabeth", constraints["Elizabeth"]["duration"], 
                            constraints["Elizabeth"]["location"], elizabeth_start, elizabeth_end)

# Meeting with Joseph
joseph_start = datetime.strptime("11:45", "%H:%M")
joseph_end = datetime.strptime("14:45", "%H:%M")
arrival_time = add_meeting("Joseph", constraints["Joseph"]["duration"], 
                            constraints["Joseph"]["location"], joseph_start, joseph_end)

# Meeting with Karen
karen_start = datetime.strptime("14:15", "%H:%M")
karen_end = datetime.strptime("22:00", "%H:%M")
arrival_time = add_meeting("Karen", constraints["Karen"]["duration"], 
                            constraints["Karen"]["location"], karen_start, karen_end)

# Meeting with Richard
richard_start = datetime.strptime("14:30", "%H:%M")
richard_end = datetime.strptime("17:30", "%H:%M")
arrival_time = add_meeting("Richard", constraints["Richard"]["duration"], 
                            constraints["Richard"]["location"], richard_start, richard_end)

# Meeting with Kimberly
kimberly_start = datetime.strptime("14:15", "%H:%M")
kimberly_end = datetime.strptime("17:30", "%H:%M")
arrival_time = add_meeting("Kimberly", constraints["Kimberly"]["duration"], 
                            constraints["Kimberly"]["location"], kimberly_start, kimberly_end)

# Meeting with Helen
helen_start = datetime.strptime("14:45", "%H:%M")
helen_end = datetime.strptime("20:45", "%H:%M")
arrival_time = add_meeting("Helen", constraints["Helen"]["duration"], 
                            constraints["Helen"]["location"], helen_start, helen_end)

# Meeting with Robert
robert_start = datetime.strptime("21:45", "%H:%M")
robert_end = datetime.strptime("22:45", "%H:%M")
arrival_time = add_meeting("Robert", constraints["Robert"]["duration"], 
                            constraints["Robert"]["location"], robert_start, robert_end)

# Meeting with Ashley
ashley_start = datetime.strptime("11:30", "%H:%M")
ashley_end = datetime.strptime("21:30", "%H:%M")
arrival_time = add_meeting("Ashley", constraints["Ashley"]["duration"], 
                            constraints["Ashley"]["location"], ashley_start, ashley_end)

# Create the JSON output
output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))