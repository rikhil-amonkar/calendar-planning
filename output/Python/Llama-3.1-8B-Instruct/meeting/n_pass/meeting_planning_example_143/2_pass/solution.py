import json
from datetime import datetime, timedelta

def calculate_travel_time(distance):
    return distance // 60

def calculate_meeting_duration(min_duration):
    return min_duration // 60

def is_valid_meeting(meeting, constraints):
    start_time = datetime.strptime(meeting['start_time'], '%H:%M')
    end_time = datetime.strptime(meeting['end_time'], '%H:%M')
    duration = (end_time - start_time).total_seconds() / 60
    return duration >= constraints['min_duration']

def compute_optimal_schedule(constraints):
    # Define travel distances and times
    travel_distances = {
        'North Beach to Pacific Heights': 8,
        'North Beach to Embarcadero': 6,
        'Pacific Heights to North Beach': 9,
        'Pacific Heights to Embarcadero': 10,
        'Embarcadero to North Beach': 5,
        'Embarcadero to Pacific Heights': 11
    }

    # Initialize schedule
    schedule = []

    # Calculate travel times
    travel_times = {key: calculate_travel_time(value) for key, value in travel_distances.items()}

    # Karen's availability
    karen_start = datetime.strptime('18:45', '%H:%M')
    karen_end = datetime.strptime('20:15', '%H:%M')
    karen_duration = calculate_meeting_duration(90)

    # Mark's availability
    mark_start = datetime.strptime('13:00', '%H:%M')
    mark_end = datetime.strptime('17:45', '%H:%M')
    mark_duration = calculate_meeting_duration(120)

    # Compute optimal schedule
    if karen_start - datetime.strptime('09:00', '%H:%M') >= timedelta(hours=9):
        # Travel to Pacific Heights
        schedule.append({
            'action': 'travel',
            'location': 'Pacific Heights',
            'person': 'Karen',
          'start_time': '09:00',
            'end_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['North Beach to Pacific Heights']))
        })
        # Meet Karen
        schedule.append({
            'action':'meet',
            'location': 'Pacific Heights',
            'person': 'Karen',
          'start_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['North Beach to Pacific Heights'])),
            'end_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['North Beach to Pacific Heights']) + karen_duration)
        })
        # Travel back to North Beach
        schedule.append({
            'action': 'travel',
            'location': 'North Beach',
            'person': 'Karen',
          'start_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['North Beach to Pacific Heights']) + karen_duration),
            'end_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['Pacific Heights to North Beach']) + calculate_travel_time(travel_distances['North Beach to Pacific Heights']) + karen_duration)
        })
    elif karen_start - datetime.strptime('09:00', '%H:%M') < timedelta(hours=9) and mark_start - datetime.strptime('09:00', '%H:%M') < timedelta(hours=9):
        # Travel to Embarcadero
        schedule.append({
            'action': 'travel',
            'location': 'Embarcadero',
            'person': 'Mark',
          'start_time': '09:00',
            'end_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['North Beach to Embarcadero']))
        })
        # Meet Mark
        schedule.append({
            'action':'meet',
            'location': 'Embarcadero',
            'person': 'Mark',
          'start_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['North Beach to Embarcadero'])),
            'end_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['North Beach to Embarcadero']) + mark_duration)
        })
        # Travel back to North Beach
        schedule.append({
            'action': 'travel',
            'location': 'North Beach',
            'person': 'Mark',
          'start_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['North Beach to Embarcadero']) + mark_duration),
            'end_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['Embarcadero to North Beach']) + calculate_travel_time(travel_distances['North Beach to Embarcadero']) + mark_duration)
        })
    elif karen_start - datetime.strptime('09:00', '%H:%M') < timedelta(hours=9) and mark_start - datetime.strptime('09:00', '%H:%M') >= timedelta(hours=9):
        # Travel to Pacific Heights
        schedule.append({
            'action': 'travel',
            'location': 'Pacific Heights',
            'person': 'Karen',
          'start_time': '09:00',
            'end_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['North Beach to Pacific Heights']))
        })
        # Meet Karen
        schedule.append({
            'action':'meet',
            'location': 'Pacific Heights',
            'person': 'Karen',
          'start_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['North Beach to Pacific Heights'])),
            'end_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['North Beach to Pacific Heights']) + karen_duration)
        })
        # Travel to Embarcadero
        schedule.append({
            'action': 'travel',
            'location': 'Embarcadero',
            'person': 'Mark',
          'start_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['North Beach to Pacific Heights']) + karen_duration),
            'end_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['Pacific Heights to Embarcadero']) + calculate_travel_time(travel_distances['North Beach to Pacific Heights']) + karen_duration)
        })
        # Meet Mark
        schedule.append({
            'action':'meet',
            'location': 'Embarcadero',
            'person': 'Mark',
          'start_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['Pacific Heights to Embarcadero']) + calculate_travel_time(travel_distances['North Beach to Pacific Heights']) + karen_duration),
            'end_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['Pacific Heights to Embarcadero']) + calculate_travel_time(travel_distances['North Beach to Pacific Heights']) + karen_duration + mark_duration)
        })
        # Travel back to North Beach
        schedule.append({
            'action': 'travel',
            'location': 'North Beach',
            'person': 'Mark',
          'start_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['Pacific Heights to Embarcadero']) + calculate_travel_time(travel_distances['North Beach to Pacific Heights']) + karen_duration + mark_duration),
            'end_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['Embarcadero to North Beach']) + calculate_travel_time(travel_distances['Pacific Heights to Embarcadero']) + calculate_travel_time(travel_distances['North Beach to Pacific Heights']) + karen_duration + mark_duration)
        })

    # Add Karen's availability
    schedule.append({
        'action': 'wait',
        'location': 'Pacific Heights',
        'person': 'Karen',
      'start_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['North Beach to Pacific Heights']) + karen_duration),
        'end_time': karen_start.strftime('%H:%M')
    })
    # Meet Karen
    schedule.append({
        'action':'meet',
        'location': 'Pacific Heights',
        'person': 'Karen',
      'start_time': karen_start.strftime('%H:%M'),
        'end_time': karen_end.strftime('%H:%M')
    })
    # Add Mark's availability
    schedule.append({
        'action': 'wait',
        'location': 'Embarcadero',
        'person': 'Mark',
      'start_time': mark_start.strftime('%H:%M'),
        'end_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['Embarcadero to North Beach']) + calculate_travel_time(travel_distances['Pacific Heights to Embarcadero']) + calculate_travel_time(travel_distances['North Beach to Pacific Heights']) + karen_duration + mark_duration)
    })
    # Meet Mark
    schedule.append({
        'action':'meet',
        'location': 'Embarcadero',
        'person': 'Mark',
      'start_time': '09:{0:02d}'.format(calculate_travel_time(travel_distances['Embarcadero to North Beach']) + calculate_travel_time(travel_distances['Pacific Heights to Embarcadero']) + calculate_travel_time(travel_distances['North Beach to Pacific Heights']) + karen_duration + mark_duration),
        'end_time': mark_end.strftime('%H:%M')
    })

    return schedule

def main():
    constraints = {
      'min_duration_karen': 90,
      'min_duration_mark': 120
    }
    schedule = compute_optimal_schedule(constraints)
    print(json.dumps({'itinerary': schedule}, indent=4))

if __name__ == "__main__":
    main()