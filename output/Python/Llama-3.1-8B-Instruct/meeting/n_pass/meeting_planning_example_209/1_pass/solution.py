import json
import itertools
import datetime

# Travel distances (in minutes)
travel_times = {
    'Sunset District': {
        'Chinatown': 30,
        'Russian Hill': 24,
        'North Beach': 29
    },
    'Chinatown': {
        'Sunset District': 29,
        'Russian Hill': 7,
        'North Beach': 3
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Chinatown': 9,
        'North Beach': 5
    },
    'North Beach': {
        'Sunset District': 27,
        'Chinatown': 6,
        'Russian Hill': 4
    }
}

# Constraints
start_time = datetime.datetime.strptime('09:00', '%H:%M')
anthony_start = datetime.datetime.strptime('13:15', '%H:%M')
anthony_end = datetime.datetime.strptime('14:30', '%H:%M')
rebecca_start = datetime.datetime.strptime('19:30', '%H:%M')
rebecca_end = datetime.datetime.strptime('21:15', '%H:%M')
melissa_start = datetime.datetime.strptime('08:15', '%H:%M')
melissa_end = datetime.datetime.strptime('13:30', '%H:%M')
min_meeting_time = {
    'Anthony': 60,
    'Rebecca': 105,
    'Melissa': 105
}

def calculate_travel_time(start, end, location):
    travel_time = travel_times[start][location]
    return datetime.timedelta(minutes=travel_time)

def is_valid_meeting(start, end, person, location):
    min_time = datetime.timedelta(minutes=min_meeting_time[person])
    return end - start >= min_time

def generate_schedule():
    schedule = []
    current_time = start_time
    locations = list(travel_times.keys())
    
    for person, start_time, end_time in [
        ('Anthony', anthony_start, anthony_end),
        ('Rebecca', rebecca_start, rebecca_end),
        ('Melissa', melissa_start, melissa_end)
    ]:
        for location in locations:
            if location == 'Sunset District':
                continue
            travel_time = calculate_travel_time('Sunset District', location, location)
            if start_time > current_time + travel_time:
                continue
            if end_time < current_time + travel_time:
                continue
            for t in itertools.product([start_time, end_time], repeat=2):
                if t[0] < current_time + travel_time and t[1] > current_time + travel_time:
                    if is_valid_meeting(t[0], t[1], person, location):
                        schedule.append({
                            'action':'meet',
                            'location': location,
                            'person': person,
                           'start_time': t[0].strftime('%H:%M'),
                            'end_time': t[1].strftime('%H:%M')
                        })
                        current_time = t[1]
                        break
    return schedule

def main():
    schedule = generate_schedule()
    itinerary = []
    current_time = start_time
    for action in schedule:
        if current_time < datetime.datetime.strptime(action['start_time'], '%H:%M'):
            itinerary.append({
                'action': 'travel',
                'location': action['location'],
               'start_time': current_time.strftime('%H:%M'),
                'end_time': datetime.datetime.strptime(action['start_time'], '%H:%M').strftime('%H:%M')
            })
            current_time = datetime.datetime.strptime(action['start_time'], '%H:%M')
        itinerary.append(action)
        current_time = datetime.datetime.strptime(action['end_time'], '%H:%M')
    itinerary.append({
        'action': 'travel',
        'location': 'Sunset District',
       'start_time': current_time.strftime('%H:%M'),
        'end_time': '23:59'
    })
    result = {
        'itinerary': itinerary
    }
    print(json.dumps(result, indent=4))

if __name__ == "__main__":
    main()