import json
from datetime import datetime, timedelta
from itertools import combinations

def compute_travel_time(distance_matrix, start, end):
    return distance_matrix[start][end]

def is_meeting_possible(schedule, person, start_time, end_time, duration):
    for meeting in schedule:
        if meeting['person'] == person and datetime.strptime(start_time, '%H:%M') < datetime.strptime(meeting['end_time'], '%H:%M') and datetime.strptime(end_time, '%H:%M') > datetime.strptime(meeting['start_time'], '%H:%M'):
            return False
    return True

def generate_meeting_schedule(distance_matrix, constraints):
    schedule = []
    people = ['Matthew', 'Karen', 'Sarah', 'Jessica', 'Stephanie', 'Mary', 'Charles', 'Nancy', 'Thomas', 'Brian']

    # Meet Stephanie first
    schedule.append({'action':'meet', 'location': 'Presidio', 'person': 'Stephanie','start_time': '07:30', 'end_time': '08:30', 'duration': 60})

    # Meet Brian next
    for start_time in range(12, 18):
        for end_time in range(13, 19):
            if is_meeting_possible(schedule, 'Brian', f"{start_time}:00", f"{end_time}:00", 60):
                schedule.append({'action':'meet', 'location': 'Marina District', 'person': 'Brian','start_time': f"{start_time}:00", 'end_time': f"{end_time}:00", 'duration': 60})
                break

    # Meet Jessica next
    for start_time in range(9, 12):
        for end_time in range(11, 14):
            if is_meeting_possible(schedule, 'Jessica', f"{start_time}:00", f"{end_time}:00", 120):
                schedule.append({'action':'meet', 'location': 'Nob Hill', 'person': 'Jessica','start_time': f"{start_time}:00", 'end_time': f"{end_time}:00", 'duration': 120})
                break

    # Meet Matthew next
    for start_time in range(13, 20):
        for end_time in range(18, 23):
            if is_meeting_possible(schedule, 'Matthew', f"{start_time}:00", f"{end_time}:00", 120):
                schedule.append({'action':'meet', 'location': 'Bayview', 'person': 'Matthew','start_time': f"{start_time}:00", 'end_time': f"{end_time}:00", 'duration': 120})
                break

    # Meet Karen next
    for start_time in range(19, 21):
        for end_time in range(20, 22):
            if is_meeting_possible(schedule, 'Karen', f"{start_time}:00", f"{end_time}:00", 90):
                schedule.append({'action':'meet', 'location': 'Chinatown', 'person': 'Karen','start_time': f"{start_time}:00", 'end_time': f"{end_time}:00", 'duration': 90})
                break

    # Meet Sarah next
    for start_time in range(20, 21):
        for end_time in range(21, 22):
            if is_meeting_possible(schedule, 'Sarah', f"{start_time}:00", f"{end_time}:00", 105):
                schedule.append({'action':'meet', 'location': 'Alamo Square', 'person': 'Sarah','start_time': f"{start_time}:00", 'end_time': f"{end_time}:00", 'duration': 105})
                break

    # Meet Mary next
    for start_time in range(17, 20):
        for end_time in range(19, 22):
            if is_meeting_possible(schedule, 'Mary', f"{start_time}:00", f"{end_time}:00", 60):
                schedule.append({'action':'meet', 'location': 'Union Square', 'person': 'Mary','start_time': f"{start_time}:00", 'end_time': f"{end_time}:00", 'duration': 60})
                break

    # Meet Charles next
    for start_time in range(17, 20):
        for end_time in range(20, 22):
            if is_meeting_possible(schedule, 'Charles', f"{start_time}:00", f"{end_time}:00", 105):
                schedule.append({'action':'meet', 'location': 'The Castro', 'person': 'Charles','start_time': f"{start_time}:00", 'end_time': f"{end_time}:00", 'duration': 105})
                break

    # Meet Nancy next
    for start_time in range(14, 18):
        for end_time in range(18, 20):
            if is_meeting_possible(schedule, 'Nancy', f"{start_time}:00", f"{end_time}:00", 15):
                schedule.append({'action':'meet', 'location': 'North Beach', 'person': 'Nancy','start_time': f"{start_time}:00", 'end_time': f"{end_time}:00", 'duration': 15})
                break

    # Meet Thomas next
    for start_time in range(13, 16):
        for end_time in range(16, 18):
            if is_meeting_possible(schedule, 'Thomas', f"{start_time}:00", f"{end_time}:00", 30):
                schedule.append({'action':'meet', 'location': 'Fisherman\'s Wharf', 'person': 'Thomas','start_time': f"{start_time}:00", 'end_time': f"{end_time}:00", 'duration': 30})
                break

    return schedule

def main():
    distance_matrix = {
        'Embarcadero': {'Embarcadero': 0, 'Bayview': 21, 'Chinatown': 7, 'Alamo Square': 19, 'Nob Hill': 10, 'Presidio': 20, 'Union Square': 10, 'The Castro': 25, 'North Beach': 5, 'Fisherman\'s Wharf': 6, 'Marina District': 12},
        'Bayview': {'Embarcadero': 19, 'Bayview': 0, 'Chinatown': 19, 'Alamo Square': 16, 'Nob Hill': 20, 'Presidio': 32, 'Union Square': 18, 'The Castro': 19, 'North Beach': 22, 'Fisherman\'s Wharf': 25, 'Marina District': 27},
        'Chinatown': {'Embarcadero': 5, 'Bayview': 20, 'Chinatown': 0, 'Alamo Square': 17, 'Nob Hill': 9, 'Presidio': 19, 'Union Square': 7, 'The Castro': 22, 'North Beach': 3, 'Fisherman\'s Wharf': 8, 'Marina District': 12},
        'Alamo Square': {'Embarcadero': 16, 'Bayview': 16, 'Chinatown': 15, 'Alamo Square': 0, 'Nob Hill': 11, 'Presidio': 17, 'Union Square': 14, 'The Castro': 8, 'North Beach': 15, 'Fisherman\'s Wharf': 19, 'Marina District': 15},
        'Nob Hill': {'Embarcadero': 9, 'Bayview': 19, 'Chinatown': 6, 'Alamo Square': 11, 'Nob Hill': 0, 'Presidio': 17, 'Union Square': 7, 'The Castro': 17, 'North Beach': 8, 'Fisherman\'s Wharf': 10, 'Marina District': 11},
        'Presidio': {'Embarcadero': 20, 'Bayview': 31, 'Chinatown': 21, 'Alamo Square': 19, 'Nob Hill': 18, 'Presidio': 0, 'Union Square': 22, 'The Castro': 21, 'North Beach': 18, 'Fisherman\'s Wharf': 19, 'Marina District': 11},
        'Union Square': {'Embarcadero': 11, 'Bayview': 15, 'Chinatown': 7, 'Alamo Square': 15, 'Nob Hill': 9, 'Presidio': 24, 'Union Square': 0, 'The Castro': 17, 'North Beach': 10, 'Fisherman\'s Wharf': 15, 'Marina District': 18},
        'The Castro': {'Embarcadero': 22, 'Bayview': 19, 'Chinatown': 22, 'Alamo Square': 8, 'Nob Hill': 16, 'Presidio': 20, 'Union Square': 19, 'The Castro': 0, 'North Beach': 20, 'Fisherman\'s Wharf': 24, 'Marina District': 21},
        'North Beach': {'Embarcadero': 6, 'Bayview': 25, 'Chinatown': 6, 'Alamo Square': 16, 'Nob Hill': 7, 'Presidio': 17, 'Union Square': 7, 'The Castro': 23, 'North Beach': 0, 'Fisherman\'s Wharf': 5, 'Marina District': 9},
        'Fisherman\'s Wharf': {'Embarcadero': 8, 'Bayview': 26, 'Chinatown': 12, 'Alamo Square': 21, 'Nob Hill': 11, 'Presidio': 17, 'Union Square': 13, 'The Castro': 27, 'North Beach': 6, 'Fisherman\'s Wharf': 0, 'Marina District': 9},
        'Marina District': {'Embarcadero': 14, 'Bayview': 27, 'Chinatown': 15, 'Alamo Square': 15, 'Nob Hill': 12, 'Presidio': 10, 'Union Square': 16, 'The Castro': 22, 'North Beach': 11, 'Fisherman\'s Wharf': 10, 'Marina District': 0}
    }

    constraints = {
        'Matthew': {'start_time': '19:15', 'end_time': '22:00', 'duration': 120},
        'Karen': {'start_time': '19:15', 'end_time': '21:15', 'duration': 90},
        'Sarah': {'start_time': '20:00', 'end_time': '21:45', 'duration': 105},
        'Jessica': {'start_time': '14:30', 'end_time': '17:45', 'duration': 120},
        'Stephanie': {'start_time': '07:30', 'end_time': '10:15', 'duration': 60},
        'Mary': {'start_time': '16:45', 'end_time': '22:30', 'duration': 60},
        'Charles': {'start_time': '16:30', 'end_time': '22:00', 'duration': 105},
        'Nancy': {'start_time': '14:45', 'end_time': '20:00', 'duration': 15},
        'Thomas': {'start_time': '13:30', 'end_time': '19:00', 'duration': 30},
        'Brian': {'start_time': '12:15', 'end_time': '18:00', 'duration': 60}
    }

    schedule = generate_meeting_schedule(distance_matrix, constraints)

    itinerary = []
    for meeting in schedule:
        start_time = datetime.strptime(meeting['start_time'], '%H:%M')
        end_time = datetime.strptime(meeting['end_time'], '%H:%M')
        travel_time = compute_travel_time(distance_matrix, itinerary[-1]['location'] if itinerary else 'Embarcadero', meeting['location'])
        travel_start_time = end_time + timedelta(minutes=travel_time)
        itinerary.append({
            'action': meeting['action'],
            'location': meeting['location'],
            'person': meeting['person'],
          'start_time': travel_start_time.strftime('%H:%M'),
            'end_time': (travel_start_time + timedelta(minutes=meeting['duration'])).strftime('%H:%M')
        })

    print(json.dumps({'itinerary': itinerary}, indent=4))

if __name__ == '__main__':
    main()