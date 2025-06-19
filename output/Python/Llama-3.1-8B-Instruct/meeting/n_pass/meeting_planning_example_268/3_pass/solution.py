import json
from datetime import datetime, timedelta

# Travel distances in minutes
travel_times = {
    'Golden Gate Park': {
        'Alamo Square': 10,
        'Presidio': 11,
        'Russian Hill': 19
    },
    'Alamo Square': {
        'Golden Gate Park': 9,
        'Presidio': 18,
        'Russian Hill': 13
    },
    'Presidio': {
        'Golden Gate Park': 12,
        'Alamo Square': 18,
        'Russian Hill': 14
    },
    'Russian Hill': {
        'Golden Gate Park': 21,
        'Alamo Square': 15,
        'Presidio': 14
    }
}

# Constraints
start_time = datetime.strptime('09:00', '%H:%M')
timothy_start = datetime.strptime('12:00', '%H:%M')
timothy_end = datetime.strptime('16:15', '%H:%M')
mark_start = datetime.strptime('18:45', '%H:%M')
mark_end = datetime.strptime('21:00', '%H:%M')
joseph_start = datetime.strptime('16:45', '%H:%M')
joseph_end = datetime.strptime('21:30', '%H:%M')
min_timothy_meeting = timedelta(minutes=105)
min_mark_meeting = timedelta(minutes=60)
min_joseph_meeting = timedelta(minutes=60)

# Initialize itinerary
itinerary = []

# Meet Timothy
timothy_meeting_start = max(start_time, timothy_start)
timothy_meeting_end = timothy_meeting_start + min_timothy_meeting
timothy_meeting_start += timedelta(minutes=travel_times['Golden Gate Park']['Alamo Square'])
itinerary.append({
    'action':'meet',
    'location': 'Alamo Square',
    'person': 'Timothy',
 'start_time': timothy_meeting_start.strftime('%H:%M'),
    'end_time': timothy_meeting_end.strftime('%H:%M')
})

# Meet Mark
mark_meeting_start = max(timothy_meeting_end, mark_start)
mark_meeting_start += timedelta(minutes=travel_times['Alamo Square']['Presidio'])
mark_meeting_end = mark_meeting_start + min_mark_meeting
itinerary.append({
    'action':'meet',
    'location': 'Presidio',
    'person': 'Mark',
 'start_time': mark_meeting_start.strftime('%H:%M'),
    'end_time': mark_meeting_end.strftime('%H:%M')
})

# Meet Joseph
joseph_meeting_start = max(mark_meeting_end, joseph_start)
joseph_meeting_start += timedelta(minutes=travel_times['Presidio']['Russian Hill'])
joseph_meeting_end = joseph_meeting_start + min_joseph_meeting
itinerary.append({
    'action':'meet',
    'location': 'Russian Hill',
    'person': 'Joseph',
 'start_time': joseph_meeting_start.strftime('%H:%M'),
    'end_time': joseph_meeting_end.strftime('%H:%M')
})

# Print itinerary as JSON
print(json.dumps({
    'itinerary': itinerary
}, indent=4))