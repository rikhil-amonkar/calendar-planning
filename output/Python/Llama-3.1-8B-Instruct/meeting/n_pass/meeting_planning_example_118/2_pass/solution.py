import json
from datetime import datetime, timedelta

def compute_meeting_schedule():
    # Define travel times in minutes
    travel_times = {
        'Bayview to Union Square': 17,
        'Bayview to Presidio': 31,
        'Union Square to Bayview': 15,
        'Union Square to Presidio': 24,
        'Presidio to Bayview': 31,
        'Presidio to Union Square': 22
    }

    # Define meeting constraints
    start_time = datetime.strptime('09:00', '%H:%M')
    richard_start_time = datetime.strptime('08:45', '%H:%M')
    richard_end_time = datetime.strptime('13:00', '%H:%M')
    charles_start_time = datetime.strptime('09:45', '%H:%M')
    charles_end_time = datetime.strptime('11:00', '%H:%M')  # Update Charles' end time to 11:00

    # Initialize schedule
    schedule = []

    # Meet Richard
    if start_time > richard_start_time:
        travel_time = travel_times['Bayview to Union Square']
        start_time += timedelta(minutes=travel_time)
    elif start_time < richard_start_time:
        travel_time = travel_times['Union Square to Bayview']
        start_time -= timedelta(minutes=travel_time)

    schedule.append({
        'action':'meet',
        'location': 'Union Square',
        'person': 'Richard',
      'start_time': start_time.strftime('%H:%M'),
        'end_time': (start_time + timedelta(minutes=120)).strftime('%H:%M')  # Update meeting duration to 2 hours
    })

    # Meet Charles
    charles_available_start_time = charles_start_time
    charles_available_end_time = charles_end_time

    if start_time > charles_start_time:
        travel_time = travel_times['Union Square to Presidio']
        start_time += timedelta(minutes=travel_time)
    elif start_time < charles_start_time:
        travel_time = travel_times['Presidio to Union Square']
        start_time -= timedelta(minutes=travel_time)

    if start_time < charles_available_end_time and start_time + timedelta(minutes=120) <= charles_available_end_time:
        schedule.append({
            'action':'meet',
            'location': 'Presidio',
            'person': 'Charles',
          'start_time': start_time.strftime('%H:%M'),
            'end_time': (start_time + timedelta(minutes=120)).strftime('%H:%M')
        })
    else:
        # If the meeting with Charles cannot be scheduled within his availability, skip it
        print("Meeting with Charles cannot be scheduled within his availability.")

    return json.dumps({'itinerary': schedule}, indent=4)

print(compute_meeting_schedule())