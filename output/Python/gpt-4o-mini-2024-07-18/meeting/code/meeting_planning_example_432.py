import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Financial District'): 19,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Financial District'): 17,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Financial District'): 5,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Embarcadero'): 4,
}

# Meeting constraints
constraints = {
    'Joseph': {'location': 'Fisherman\'s Wharf', 'start': '08:00', 'end': '17:30', 'duration': 90},
    'Jeffrey': {'location': 'Bayview', 'start': '17:30', 'end': '21:30', 'duration': 60},
    'Kevin': {'location': 'Mission District', 'start': '11:15', 'end': '15:15', 'duration': 30},
    'David': {'location': 'Embarcadero', 'start': '08:15', 'end': '09:00', 'duration': 30},
    'Barbara': {'location': 'Financial District', 'start': '10:30', 'end': '16:30', 'duration': 15},
}

def schedule_meetings():
    itinerary = []
    start_time = datetime.strptime("09:00", "%H:%M")
    
    # Meeting David at Embarcadero first, as it's close by and available early
    end_time = start_time + timedelta(minutes=30)
    itinerary.append({
        "action": "meet",
        "location": "Embarcadero",
        "person": "David",
        "start_time": start_time.strftime("%H:%M"),
        "end_time": end_time.strftime("%H:%M")
    })
    
    # After meeting David, head to Financial District to meet Barbara
    travel_time = travel_times[('Embarcadero', 'Financial District')]
    start_time = end_time + timedelta(minutes=travel_time)
    end_time = start_time + timedelta(minutes=15)
    itinerary.append({
        "action": "meet",
        "location": "Financial District",
        "person": "Barbara",
        "start_time": start_time.strftime("%H:%M"),
        "end_time": end_time.strftime("%H:%M")
    })
    
    # Next, go to Mission District to meet Kevin
    travel_time = travel_times[('Financial District', 'Mission District')]
    start_time = end_time + timedelta(minutes=travel_time)
    end_time = start_time + timedelta(minutes=30)
    itinerary.append({
        "action": "meet",
        "location": "Mission District",
        "person": "Kevin",
        "start_time": start_time.strftime("%H:%M"),
        "end_time": end_time.strftime("%H:%M")
    })

    # Next, head to Fisherman's Wharf to meet Joseph
    travel_time = travel_times[('Mission District', 'Fisherman\'s Wharf')]
    start_time = end_time + timedelta(minutes=travel_time)
    end_time = start_time + timedelta(minutes=90)  # Meet Joseph for 90 minutes
    itinerary.append({
        "action": "meet",
        "location": "Fisherman\'s Wharf",
        "person": "Joseph",
        "start_time": start_time.strftime("%H:%M"),
        "end_time": end_time.strftime("%H:%M")
    })

    # Finally, go to Bayview to meet Jeffrey
    travel_time = travel_times[('Fisherman\'s Wharf', 'Bayview')]
    start_time = end_time + timedelta(minutes=travel_time)
    end_time = start_time + timedelta(minutes=60)  # Meet Jeffrey for 60 minutes
    itinerary.append({
        "action": "meet",
        "location": "Bayview",
        "person": "Jeffrey",
        "start_time": start_time.strftime("%H:%M"),
        "end_time": end_time.strftime("%H:%M")
    })
    
    # Return the schedule as a JSON object
    return json.dumps({"itinerary": itinerary}, indent=2)

if __name__ == "__main__":
    print(schedule_meetings())