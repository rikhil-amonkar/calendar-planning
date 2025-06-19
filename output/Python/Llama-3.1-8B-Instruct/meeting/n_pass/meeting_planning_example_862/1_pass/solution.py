import json
from datetime import datetime, timedelta

def calculate_travel_time(start, end, locations):
    travel_times = {
        'Mission District': {'Alamo Square': 10, 'Presidio': 25, 'Russian Hill': 15, 'North Beach': 17, 'Golden Gate Park': 17, 'Richmond District': 20, 'Embarcadero': 19, 'Financial District': 15, 'Marina District': 19},
        'Alamo Square': {'Mission District': 10, 'Presidio': 17, 'Russian Hill': 13, 'North Beach': 15, 'Golden Gate Park': 9, 'Richmond District': 11, 'Embarcadero': 16, 'Financial District': 17, 'Marina District': 15},
        'Presidio': {'Mission District': 26, 'Alamo Square': 19, 'Russian Hill': 14, 'North Beach': 18, 'Golden Gate Park': 12, 'Richmond District': 7, 'Embarcadero': 20, 'Financial District': 23, 'Marina District': 11},
        'Russian Hill': {'Mission District': 16, 'Alamo Square': 15, 'Presidio': 14, 'North Beach': 5, 'Golden Gate Park': 21, 'Richmond District': 14, 'Embarcadero': 8, 'Financial District': 11, 'Marina District': 7},
        'North Beach': {'Mission District': 18, 'Alamo Square': 16, 'Presidio': 17, 'Russian Hill': 4, 'Golden Gate Park': 22, 'Richmond District': 18, 'Embarcadero': 6, 'Financial District': 8, 'Marina District': 9},
        'Golden Gate Park': {'Mission District': 17, 'Alamo Square': 9, 'Presidio': 11, 'Russian Hill': 19, 'North Beach': 23, 'Richmond District': 7, 'Embarcadero': 25, 'Financial District': 26, 'Marina District': 16},
        'Richmond District': {'Mission District': 20, 'Alamo Square': 13, 'Presidio': 7, 'Russian Hill': 13, 'North Beach': 17, 'Golden Gate Park': 9, 'Embarcadero': 21, 'Financial District': 22, 'Marina District': 9},
        'Embarcadero': {'Mission District': 19, 'Alamo Square': 19, 'Presidio': 20, 'Russian Hill': 8, 'North Beach': 5, 'Golden Gate Park': 25, 'Richmond District': 21, 'Financial District': 5, 'Marina District': 12},
        'Financial District': {'Mission District': 15, 'Alamo Square': 17, 'Presidio': 22, 'Russian Hill': 11, 'North Beach': 7, 'Golden Gate Park': 23, 'Richmond District': 21, 'Embarcadero': 4, 'Marina District': 15},
        'Marina District': {'Mission District': 20, 'Alamo Square': 15, 'Presidio': 10, 'Russian Hill': 8, 'North Beach': 11, 'Golden Gate Park': 18, 'Richmond District': 11, 'Embarcadero': 14, 'Financial District': 17}
    }
    start_time = datetime.strptime(start, '%H:%M')
    end_time = datetime.strptime(end, '%H:%M')
    travel_time = timedelta(minutes=0)
    for location in locations:
        travel_time += timedelta(minutes=travel_times[start][location])
        start_time += travel_time
    return start_time.strftime('%H:%M')

def compute_schedule(locations, times, durations):
    schedule = []
    for person in locations:
        for location in locations[person]:
            if location in times and times[location] and (times[location][0] - times[location][1]).total_seconds() >= durations[person]:
                start_time = calculate_travel_time('09:00', times[location][0].strftime('%H:%M'), [person, location])
                end_time = calculate_travel_time(times[location][0].strftime('%H:%M'), times[location][1].strftime('%H:%M'), [person, location])
                schedule.append({'action':'meet', 'location': location, 'person': person,'start_time': start_time, 'end_time': end_time})
    return schedule

def main():
    locations = {
        'Laura': ['Alamo Square'],
        'Brian': ['Presidio'],
        'Karen': ['Russian Hill'],
        'Stephanie': ['North Beach'],
        'Helen': ['Golden Gate Park'],
        'Sandra': ['Richmond District'],
        'Mary': ['Embarcadero'],
        'Deborah': ['Financial District'],
        'Elizabeth': ['Marina District']
    }
    times = {
        'Laura': [(datetime.strptime('14:30', '%H:%M'), datetime.strptime('16:15', '%H:%M'))],
        'Brian': [(datetime.strptime('10:15', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
        'Karen': [(datetime.strptime('18:00', '%H:%M'), datetime.strptime('20:15', '%H:%M'))],
        'Stephanie': [(datetime.strptime('10:15', '%H:%M'), datetime.strptime('16:00', '%H:%M'))],
        'Helen': [(datetime.strptime('11:30', '%H:%M'), datetime.strptime('21:45', '%H:%M'))],
        'Sandra': [(datetime.strptime('08:00', '%H:%M'), datetime.strptime('15:15', '%H:%M'))],
        'Mary': [(datetime.strptime('16:45', '%H:%M'), datetime.strptime('18:45', '%H:%M'))],
        'Deborah': [(datetime.strptime('19:00', '%H:%M'), datetime.strptime('20:45', '%H:%M'))],
        'Elizabeth': [(datetime.strptime('08:30', '%H:%M'), datetime.strptime('13:15', '%H:%M'))]
    }
    durations = {
        'Laura': 75,
        'Brian': 30,
        'Karen': 90,
        'Stephanie': 75,
        'Helen': 120,
        'Sandra': 30,
        'Mary': 120,
        'Deborah': 105,
        'Elizabeth': 105
    }
    schedule = compute_schedule(locations, times, durations)
    print(json.dumps({'itinerary': schedule}, indent=4))

if __name__ == "__main__":
    main()