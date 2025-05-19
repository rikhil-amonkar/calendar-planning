import json
from datetime import datetime, timedelta

# Define travel times (in minutes) as a nested dictionary
travel_times = {
    "Chinatown": {
        "Embarcadero": 5,
        "Pacific Heights": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 19,
        "Golden Gate Park": 23,
        "Fisherman's Wharf": 8,
        "Sunset District": 29,
        "The Castro": 22
    },
    "Embarcadero": {
        "Chinatown": 7,
        "Pacific Heights": 11,
        "Russian Hill": 8,
        "Haight-Ashbury": 21,
        "Golden Gate Park": 25,
        "Fisherman's Wharf": 6,
        "Sunset District": 30,
        "The Castro": 25
    },
    "Pacific Heights": {
        "Chinatown": 11,
        "Embarcadero": 10,
        "Russian Hill": 7,
        "Haight-Ashbury": 11,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Sunset District": 21,
        "The Castro": 16
    },
    "Russian Hill": {
        "Chinatown": 9,
        "Embarcadero": 8,
        "Pacific Heights": 7,
        "Haight-Ashbury": 17,
        "Golden Gate Park": 21,
        "Fisherman's Wharf": 7,
        "Sunset District": 23,
        "The Castro": 21
    },
    "Haight-Ashbury": {
        "Chinatown": 19,
        "Embarcadero": 20,
        "Pacific Heights": 12,
        "Russian Hill": 17,
        "Golden Gate Park": 7,
        "Fisherman's Wharf": 23,
        "Sunset District": 15,
        "The Castro": 6
    },
    "Golden Gate Park": {
        "Chinatown": 23,
        "Embarcadero": 25,
        "Pacific Heights": 16,
        "Russian Hill": 19,
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "Sunset District": 10,
        "The Castro": 13
    },
    "Fisherman's Wharf": {
        "Chinatown": 12,
        "Embarcadero": 8,
        "Pacific Heights": 12,
        "Russian Hill": 7,
        "Haight-Ashbury": 22,
        "Golden Gate Park": 25,
        "Sunset District": 29,
        "The Castro": 27
    },
    "Sunset District": {
        "Chinatown": 30,
        "Embarcadero": 30,
        "Pacific Heights": 21,
        "Russian Hill": 24,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 29,
        "The Castro": 17
    },
    "The Castro": {
        "Chinatown": 22,
        "Embarcadero": 22,
        "Pacific Heights": 16,
        "Russian Hill": 18,
        "Haight-Ashbury": 6,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 24,
        "Sunset District": 17
    }
}

# Define meeting constraints
meetings = {
    "Richard": {"location": "Embarcadero", "available": (datetime.strptime('15:15', '%H:%M'), datetime.strptime('18:45', '%H:%M')), "duration": 90},
    "Mark": {"location": "Pacific Heights", "available": (datetime.strptime('15:00', '%H:%M'), datetime.strptime('17:00', '%H:%M')), "duration": 45},
    "Matthew": {"location": "Russian Hill", "available": (datetime.strptime('17:30', '%H:%M'), datetime.strptime('21:00', '%H:%M')), "duration": 90},
    "Rebecca": {"location": "Haight-Ashbury", "available": (datetime.strptime('14:45', '%H:%M'), datetime.strptime('18:00', '%H:%M')), "duration": 60},
    "Melissa": {"location": "Golden Gate Park", "available": (datetime.strptime('13:45', '%H:%M'), datetime.strptime('17:30', '%H:%M')), "duration": 90},
    "Margaret": {"location": "Fisherman's Wharf", "available": (datetime.strptime('14:45', '%H:%M'), datetime.strptime('20:15', '%H:%M')), "duration": 15},
    "Emily": {"location": "Sunset District", "available": (datetime.strptime('15:45', '%H:%M'), datetime.strptime('17:00', '%H:%M')), "duration": 45},
    "George": {"location": "The Castro", "available": (datetime.strptime('14:00', '%H:%M'), datetime.strptime('16:15', '%H:%M')), "duration": 75},
}

# Calculate and build itinerary
def schedule_meetings():
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('21:00', '%H:%M')
    itinerary = []
    current_time = start_time
    current_location = "Chinatown"

    while current_time < end_time:
        for person, details in meetings.items():
            location = details['location']
            available_start, available_end = details['available']
            duration = details['duration']

            travel_time = travel_times[current_location][location]
            start_meeting_time = current_time + timedelta(minutes=travel_time)

            if start_meeting_time < available_start:
                current_time = available_start - timedelta(minutes=travel_time)
                start_meeting_time = current_time + timedelta(minutes=travel_time)

            end_meeting_time = start_meeting_time + timedelta(minutes=duration)

            if available_start <= start_meeting_time < available_end and end_meeting_time <= available_end:
                itinerary.append({
                    "action": "meet",
                    "location": location,
                    "person": person,
                    "start_time": start_meeting_time.strftime('%H:%M'),
                    "end_time": end_meeting_time.strftime('%H:%M')
                })
                current_time = end_meeting_time + timedelta(minutes=travel_time)
                current_location = location
                break
    return {"itinerary": itinerary}

# Execute scheduling
result = schedule_meetings()

# Output result in JSON format
print(json.dumps(result, indent=2))