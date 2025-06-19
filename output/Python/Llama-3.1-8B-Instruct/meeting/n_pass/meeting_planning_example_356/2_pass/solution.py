import json
from datetime import datetime, timedelta

def calculate_travel_time(start, end, travel_time):
    start_hour, start_minute = map(int, start.split(':'))
    end_hour, end_minute = map(int, end.split(':'))
    travel_hours = travel_time // 60
    travel_minutes = travel_time % 60
    travel_start = datetime(2024, 1, 1, start_hour, start_minute)
    travel_end = travel_start + timedelta(hours=travel_hours, minutes=travel_minutes)
    return travel_end.strftime('%H:%M')

def compute_meeting_schedule():
    travel_distances = {
        'Bayview': {
            'North Beach': 21,
            'Presidio': 31,
            'Haight-Ashbury': 19,
            'Union Square': 17
        },
        'North Beach': {
            'Bayview': 22,
            'Presidio': 17,
            'Haight-Ashbury': 18,
            'Union Square': 7
        },
        'Presidio': {
            'Bayview': 31,
            'North Beach': 18,
            'Haight-Ashbury': 15,
            'Union Square': 22
        },
        'Haight-Ashbury': {
            'Bayview': 18,
            'North Beach': 19,
            'Presidio': 15,
            'Union Square': 17
        },
        'Union Square': {
            'Bayview': 15,
            'North Beach': 10,
            'Presidio': 24,
            'Haight-Ashbury': 18
        }
    }

    constraints = {
        'Barbara': {'location': 'North Beach','start_time': '13:45', 'end_time': '20:15','meeting_time': 60},
        'Margaret': {'location': 'Presidio','start_time': '10:15', 'end_time': '15:15','meeting_time': 30},
        'Kevin': {'location': 'Haight-Ashbury','start_time': '20:00', 'end_time': '20:45','meeting_time': 30},
        'Kimberly': {'location': 'Union Square','start_time': '07:45', 'end_time': '16:45','meeting_time': 30}
    }

    current_location = 'Bayview'
    start_time = '09:00'
    schedule = []
    current_time = datetime(2024, 1, 1, 9, 0)

    for person in constraints:
        location = constraints[person]['location']
        start = constraints[person]['start_time']
        end = constraints[person]['end_time']
        meeting_time = constraints[person]['meeting_time']

        # Check if person is available
        person_start_time = datetime(2024, 1, 1, int(start.split(':')[0]), int(start.split(':')[1]))
        person_end_time = datetime(2024, 1, 1, int(end.split(':')[0]), int(end.split(':')[1]))

        # Check if meeting is possible
        if person_start_time >= current_time:
            # Calculate travel time
            travel_time = travel_distances[current_location][location]

            # Check if travel time allows for meeting
            if (person_start_time + timedelta(minutes=meeting_time)) >= (current_time + timedelta(minutes=travel_time)):
                # Add meeting to schedule
                schedule.append({
                    'action':'meet',
                    'location': location,
                    'person': person,
                  'start_time': current_time.strftime('%H:%M'),
                    'end_time': (current_time + timedelta(minutes=travel_time + meeting_time)).strftime('%H:%M')
                })

                # Update current location and time
                current_location = location
                current_time = (current_time + timedelta(minutes=travel_time + meeting_time))

                # Update start time
                start_time = (current_time + timedelta(minutes=meeting_time)).strftime('%H:%M')

                # Update current time
                current_time = datetime(2024, 1, 1, int(start_time.split(':')[0]), int(start_time.split(':')[1]))

        # If person is not available, try to meet before their start time
        else:
            # Calculate travel time
            travel_time = travel_distances[current_location][location]

            # Calculate meeting end time
            meeting_end_time = person_start_time - timedelta(minutes=travel_time)

            # Check if meeting is possible
            if meeting_end_time >= current_time:
                # Add meeting to schedule
                schedule.append({
                    'action':'meet',
                    'location': location,
                    'person': person,
                  'start_time': current_time.strftime('%H:%M'),
                    'end_time': meeting_end_time.strftime('%H:%M')
                })

                # Update current location and time
                current_location = location
                current_time = meeting_end_time

    # Check if Barbara is available at her start time
    if 'Barbara' in constraints and constraints['Barbara']['start_time']!= '09:00':
        # Find the earliest time that Barbara is available
        earliest_available_time = datetime(2024, 1, 1, int(constraints['Barbara']['start_time'].split(':')[0]), int(constraints['Barbara']['start_time'].split(':')[1]))

        # Calculate travel time
        travel_time = travel_distances['Bayview']['North Beach']

        # Check if travel time allows for meeting
        if earliest_available_time >= current_time:
            # Add meeting to schedule
            schedule.append({
                'action':'meet',
                'location': 'North Beach',
                'person': 'Barbara',
              'start_time': current_time.strftime('%H:%M'),
                'end_time': (current_time + timedelta(minutes=travel_time + 60)).strftime('%H:%M')
            })

            # Update current location and time
            current_location = 'North Beach'
            current_time = (current_time + timedelta(minutes=travel_time + 60))

    # Add travel time to Bayview
    schedule.append({
        'action': 'travel',
        'location': 'Bayview',
        'person': 'You',
      'start_time': current_time.strftime('%H:%M'),
        'end_time': (current_time + timedelta(minutes=travel_distances[current_location]['Bayview'])).strftime('%H:%M')
    })

    return schedule

def main():
    schedule = compute_meeting_schedule()
    itinerary = []
    for event in schedule:
        if event['action'] =='meet':
            itinerary.append({
                'action':'meet',
                'location': event['location'],
                'person': event['person'],
              'start_time': event['start_time'],
                'end_time': event['end_time']
            })
        elif event['action'] == 'travel':
            itinerary.append({
                'action': 'travel',
                'location': event['location'],
                'person': event['person'],
              'start_time': event['start_time'],
                'end_time': event['end_time']
            })
    result = {
        'itinerary': itinerary
    }
    print(json.dumps(result, indent=4))

if __name__ == "__main__":
    main()