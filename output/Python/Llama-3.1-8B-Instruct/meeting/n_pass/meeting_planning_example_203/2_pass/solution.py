import json
from datetime import datetime, timedelta

# Travel distances (in minutes)
travel_times = {
    'Financial District to Fisherman\'s Wharf': 10,
    'Financial District to Pacific Heights': 13,
    'Financial District to Mission District': 17,
    'Fisherman\'s Wharf to Financial District': 11,
    'Fisherman\'s Wharf to Pacific Heights': 12,
    'Fisherman\'s Wharf to Mission District': 22,
    'Pacific Heights to Financial District': 13,
    'Pacific Heights to Fisherman\'s Wharf': 12,
    'Pacific Heights to Mission District': 15,
    'Mission District to Financial District': 17,
    'Mission District to Fisherman\'s Wharf': 22,
    'Mission District to Pacific Heights': 16
}

# Constraints
arrival_time = datetime.strptime('09:00', '%H:%M')
david_start_time = datetime.strptime('10:45', '%H:%M')
david_end_time = datetime.strptime('15:30', '%H:%M')
timothy_start_time = datetime.strptime('09:00', '%H:%M')
timothy_end_time = datetime.strptime('15:30', '%H:%M')
robert_start_time = datetime.strptime('12:15', '%H:%M')
robert_end_time = datetime.strptime('19:45', '%H:%M')
min_meeting_time_david = timedelta(minutes=15)
min_meeting_time_timothy = timedelta(minutes=75)
min_meeting_time_robert = timedelta(minutes=90)

# Compute optimal meeting schedule
itinerary = []
current_time = arrival_time

# Meet Timothy
itinerary.append({
    'action':'meet',
    'location': 'Financial District',
    'person': 'Timothy',
  'start_time': current_time.strftime('%H:%M'),
    'end_time': (current_time + min_meeting_time_timothy).strftime('%H:%M')
})
current_time += min_meeting_time_timothy

# Travel to Fisherman's Wharf
current_time += timedelta(minutes=travel_times['Financial District to Fisherman\'s Wharf'])
itinerary.append({
    'action': 'travel',
    'location': 'Financial District',
    'person': 'David',
  'start_time': current_time.strftime('%H:%M'),
    'end_time': (current_time + timedelta(minutes=travel_times['Fisherman\'s Wharf to Financial District'])).strftime('%H:%M')
})
current_time += timedelta(minutes=travel_times['Fisherman\'s Wharf to Financial District'])

# Meet David
if david_start_time < current_time:
    itinerary.append({
        'action':'meet',
        'location': 'Fisherman\'s Wharf',
        'person': 'David',
      'start_time': current_time.strftime('%H:%M'),
        'end_time': (current_time + min_meeting_time_david).strftime('%H:%M')
    })
    current_time += min_meeting_time_david
    # Travel to Mission District
    current_time += timedelta(minutes=travel_times['Fisherman\'s Wharf to Mission District'])
    itinerary.append({
        'action': 'travel',
        'location': 'Fisherman\'s Wharf',
        'person': 'Robert',
      'start_time': current_time.strftime('%H:%M'),
        'end_time': (current_time + timedelta(minutes=travel_times['Mission District to Fisherman\'s Wharf'])).strftime('%H:%M')
    })
    current_time += timedelta(minutes=travel_times['Mission District to Fisherman\'s Wharf'])

# Meet Robert
if robert_start_time < current_time:
    itinerary.append({
        'action':'meet',
        'location': 'Mission District',
        'person': 'Robert',
      'start_time': current_time.strftime('%H:%M'),
        'end_time': (current_time + min_meeting_time_robert).strftime('%H:%M')
    })
    current_time += min_meeting_time_robert

# Add remaining time to itinerary
while current_time < david_end_time:
    # Travel to Fisherman's Wharf
    current_time += timedelta(minutes=travel_times['Mission District to Fisherman\'s Wharf'])
    itinerary.append({
        'action': 'travel',
        'location': 'Mission District',
        'person': 'David',
      'start_time': current_time.strftime('%H:%M'),
        'end_time': (current_time + timedelta(minutes=travel_times['Fisherman\'s Wharf to Mission District'])).strftime('%H:%M')
    })
    current_time += timedelta(minutes=travel_times['Fisherman\'s Wharf to Mission District'])
    # Meet David
    itinerary.append({
        'action':'meet',
        'location': 'Fisherman\'s Wharf',
        'person': 'David',
      'start_time': current_time.strftime('%H:%M'),
        'end_time': (current_time + min_meeting_time_david).strftime('%H:%M')
    })
    current_time += min_meeting_time_david

# Output result as JSON
print(json.dumps({'itinerary': itinerary}, indent=4))