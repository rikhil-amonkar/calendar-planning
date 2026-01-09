import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times dictionary (in minutes)
    travel_times = {
        ('Chinatown', 'Mission District'): 18,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Presidio'): 19,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'Alamo Square'): 11,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Union Square'): 15,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Presidio'): 25,
        ('Alamo Square', 'Chinatown'): 16,
        ('Alamo Square', 'Mission District'): 10,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'Presidio'): 18,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Sunset District'): 21,
        ('Pacific Heights', 'Presidio'): 11,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Mission District'): 14,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Golden Gate Park'): 22,
        ('Union Square', 'Sunset District'): 26,
        ('Union Square', 'Presidio'): 24,
        ('Golden Gate Park', 'Chinatown'): 23,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Pacific Heights'): 16,
        ('Golden Gate Park', 'Union Square'): 22,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Alamo Square'): 17,
        ('Sunset District', 'Pacific Heights'): 21,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Sunset District', 'Presidio'): 16,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Mission District'): 26,
        ('Presidio', 'Alamo Square'): 18,
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Sunset District'): 15
    }

    # Friend availability and constraints
    friends = {
        'David': {
            'location': 'Mission District',
            'available_start': datetime.strptime('8:00', '%H:%M'),
            'available_end': datetime.strptime('19:45', '%H:%M'),
            'min_duration': 45
        },
        'Kenneth': {
            'location': 'Alamo Square',
            'available_start': datetime.strptime('14:00', '%H:%M'),
            'available_end': datetime.strptime('19:45', '%H:%M'),
            'min_duration': 120
        },
        'John': {
            'location': 'Pacific Heights',
            'available_start': datetime.strptime('17:00', '%H:%M'),
            'available_end': datetime.strptime('20:00', '%H:%M'),
            'min_duration': 15
        },
        'Charles': {
            'location': 'Union Square',
            'available_start': datetime.strptime('21:45', '%H:%M'),
            'available_end': datetime.strptime('22:45', '%H:%M'),
            'min_duration': 60
        },
        'Deborah': {
            'location': 'Golden Gate Park',
            'available_start': datetime.strptime('7:00', '%H:%M'),
            'available_end': datetime.strptime('18:15', '%H:%M'),
            'min_duration': 90
        },
        'Karen': {
            'location': 'Sunset District',
            'available_start': datetime.strptime('17:45', '%H:%M'),
            'available_end': datetime.strptime('21:15', '%H:%M'),
            'min_duration': 15
        },
        'Carol': {
            'location': 'Presidio',
            'available_start': datetime.strptime('8:15', '%H:%M'),
            'available_end': datetime.strptime('9:15', '%H:%M'),
            'min_duration': 30
        }
    }

    # Start at Chinatown at 9:00
    current_time = datetime.strptime('9:00', '%H:%M')
    current_location = 'Chinatown'
    
    itinerary = []
    
    # Try to meet Carol first (only available in the morning)
    carol = friends['Carol']
    travel_time = travel_times[(current_location, carol['location'])]
    arrival_time = current_time + timedelta(minutes=travel_time)
    
    if (arrival_time >= carol['available_start'] and 
        arrival_time + timedelta(minutes=carol['min_duration']) <= carol['available_end']):
        itinerary.append({
            'action': 'meet',
            'location': carol['location'],
            'person': 'Carol',
            'start_time': arrival_time.strftime('%H:%M'),
            'end_time': (arrival_time + timedelta(minutes=carol['min_duration'])).strftime('%H:%M')
        })
        current_time = arrival_time + timedelta(minutes=carol['min_duration'])
        current_location = carol['location']
    
    # Try to meet David next
    david = friends['David']
    travel_time = travel_times[(current_location, david['location'])]
    arrival_time = current_time + timedelta(minutes=travel_time)
    
    if (arrival_time >= david['available_start'] and 
        arrival_time + timedelta(minutes=david['min_duration']) <= david['available_end']):
        itinerary.append({
            'action': 'meet',
            'location': david['location'],
            'person': 'David',
            'start_time': arrival_time.strftime('%H:%M'),
            'end_time': (arrival_time + timedelta(minutes=david['min_duration'])).strftime('%H:%M')
        })
        current_time = arrival_time + timedelta(minutes=david['min_duration'])
        current_location = david['location']
    
    # Try to meet Deborah next
    deborah = friends['Deborah']
    travel_time = travel_times[(current_location, deborah['location'])]
    arrival_time = current_time + timedelta(minutes=travel_time)
    
    if (arrival_time >= deborah['available_start'] and 
        arrival_time + timedelta(minutes=deborah['min_duration']) <= deborah['available_end']):
        itinerary.append({
            'action': 'meet',
            'location': deborah['location'],
            'person': 'Deborah',
            'start_time': arrival_time.strftime('%H:%M'),
            'end_time': (arrival_time + timedelta(minutes=deborah['min_duration'])).strftime('%H:%M')
        })
        current_time = arrival_time + timedelta(minutes=deborah['min_duration'])
        current_location = deborah['location']
    
    # Try to meet Kenneth next
    kenneth = friends['Kenneth']
    travel_time = travel_times[(current_location, kenneth['location'])]
    arrival_time = current_time + timedelta(minutes=travel_time)
    
    if (arrival_time >= kenneth['available_start'] and 
        arrival_time + timedelta(minutes=kenneth['min_duration']) <= kenneth['available_end']):
        itinerary.append({
            'action': 'meet',
            'location': kenneth['location'],
            'person': 'Kenneth',
            'start_time': arrival_time.strftime('%H:%M'),
            'end_time': (arrival_time + timedelta(minutes=kenneth['min_duration'])).strftime('%H:%M')
        })
        current_time = arrival_time + timedelta(minutes=kenneth['min_duration'])
        current_location = kenneth['location']
    
    # Try to meet Karen next
    karen = friends['Karen']
    travel_time = travel_times[(current_location, karen['location'])]
    arrival_time = current_time + timedelta(minutes=travel_time)
    
    if (arrival_time >= karen['available_start'] and 
        arrival_time + timedelta(minutes=karen['min_duration']) <= karen['available_end']):
        itinerary.append({
            'action': 'meet',
            'location': karen['location'],
            'person': 'Karen',
            'start_time': arrival_time.strftime('%H:%M'),
            'end_time': (arrival_time + timedelta(minutes=karen['min_duration'])).strftime('%H:%M')
        })
        current_time = arrival_time + timedelta(minutes=karen['min_duration'])
        current_location = karen['location']
    
    # Try to meet John next
    john = friends['John']
    travel_time = travel_times[(current_location, john['location'])]
    arrival_time = current_time + timedelta(minutes=travel_time)
    
    if (arrival_time >= john['available_start'] and 
        arrival_time + timedelta(minutes=john['min_duration']) <= john['available_end']):
        itinerary.append({
            'action': 'meet',
            'location': john['location'],
            'person': 'John',
            'start_time': arrival_time.strftime('%H:%M'),
            'end_time': (arrival_time + timedelta(minutes=john['min_duration'])).strftime('%H:%M')
        })
        current_time = arrival_time + timedelta(minutes=john['min_duration'])
        current_location = john['location']
    
    # Try to meet Charles last
    charles = friends['Charles']
    travel_time = travel_times[(current_location, charles['location'])]
    arrival_time = current_time + timedelta(minutes=travel_time)
    
    if (arrival_time >= charles['available_start'] and 
        arrival_time + timedelta(minutes=charles['min_duration']) <= charles['available_end']):
        itinerary.append({
            'action': 'meet',
            'location': charles['location'],
            'person': 'Charles',
            'start_time': arrival_time.strftime('%H:%M'),
            'end_time': (arrival_time + timedelta(minutes=charles['min_duration'])).strftime('%H:%M')
        })
    
    # Output the result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()