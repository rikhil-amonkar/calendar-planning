import json
from datetime import datetime, timedelta

class Meeting:
    def __init__(self, person, location, start_time, end_time):
        self.person = person
        self.location = location
        self.start_time = start_time
        self.end_time = end_time

    def duration(self):
        return (datetime.strptime(self.end_time, '%H:%M') - datetime.strptime(self.start_time, '%H:%M')).total_seconds() / 60

class Schedule:
    def __init__(self):
        self.meetings = []
        self.travel_times = {
            'Bayview': {
                'North Beach': 22,
                'Fisherman\'s Wharf': 25,
                'Haight-Ashbury': 19,
                'Nob Hill': 20,
                'Golden Gate Park': 22,
                'Union Square': 18,
                'Alamo Square': 16,
                'Presidio': 32,
                'Chinatown': 19,
                'Pacific Heights': 23
            },
            'North Beach': {
                'Bayview': 25,
                'Fisherman\'s Wharf': 5,
                'Haight-Ashbury': 18,
                'Nob Hill': 7,
                'Golden Gate Park': 22,
                'Union Square': 7,
                'Alamo Square': 16,
                'Presidio': 17,
                'Chinatown': 6,
                'Pacific Heights': 8
            },
            'Fisherman\'s Wharf': {
                'Bayview': 26,
                'North Beach': 6,
                'Haight-Ashbury': 22,
                'Nob Hill': 11,
                'Golden Gate Park': 25,
                'Union Square': 13,
                'Alamo Square': 21,
                'Presidio': 17,
                'Chinatown': 12,
                'Pacific Heights': 12
            },
            'Haight-Ashbury': {
                'Bayview': 18,
                'North Beach': 19,
                'Fisherman\'s Wharf': 23,
                'Nob Hill': 15,
                'Golden Gate Park': 7,
                'Union Square': 19,
                'Alamo Square': 5,
                'Presidio': 15,
                'Chinatown': 19,
                'Pacific Heights': 12
            },
            'Nob Hill': {
                'Bayview': 19,
                'North Beach': 8,
                'Fisherman\'s Wharf': 10,
                'Haight-Ashbury': 13,
                'Golden Gate Park': 17,
                'Union Square': 7,
                'Alamo Square': 11,
                'Presidio': 17,
                'Chinatown': 6,
                'Pacific Heights': 8
            },
            'Golden Gate Park': {
                'Bayview': 23,
                'North Beach': 23,
                'Fisherman\'s Wharf': 24,
                'Haight-Ashbury': 7,
                'Nob Hill': 20,
                'Union Square': 22,
                'Alamo Square': 9,
                'Presidio': 11,
                'Chinatown': 23,
                'Pacific Heights': 16
            },
            'Union Square': {
                'Bayview': 15,
                'North Beach': 10,
                'Fisherman\'s Wharf': 15,
                'Haight-Ashbury': 18,
                'Nob Hill': 9,
                'Golden Gate Park': 22,
                'Alamo Square': 15,
                'Presidio': 24,
                'Chinatown': 7,
                'Pacific Heights': 15
            },
            'Alamo Square': {
                'Bayview': 16,
                'North Beach': 15,
                'Fisherman\'s Wharf': 19,
                'Haight-Ashbury': 5,
                'Nob Hill': 11,
                'Golden Gate Park': 9,
                'Union Square': 14,
                'Presidio': 17,
                'Chinatown': 15,
                'Pacific Heights': 10
            },
            'Presidio': {
                'Bayview': 31,
                'North Beach': 18,
                'Fisherman\'s Wharf': 19,
                'Haight-Ashbury': 15,
                'Nob Hill': 18,
                'Golden Gate Park': 12,
                'Union Square': 22,
                'Alamo Square': 19,
                'Chinatown': 21,
                'Pacific Heights': 11
            },
            'Chinatown': {
                'Bayview': 20,
                'North Beach': 3,
                'Fisherman\'s Wharf': 8,
                'Haight-Ashbury': 19,
                'Nob Hill': 9,
                'Golden Gate Park': 23,
                'Union Square': 7,
                'Alamo Square': 17,
                'Presidio': 19,
                'Pacific Heights': 10
            },
            'Pacific Heights': {
                'Bayview': 22,
                'North Beach': 9,
                'Fisherman\'s Wharf': 13,
                'Haight-Ashbury': 11,
                'Nob Hill': 8,
                'Golden Gate Park': 15,
                'Union Square': 12,
                'Alamo Square': 10,
                'Presidio': 11,
                'Chinatown': 11
            }
        }

    def add_meeting(self, meeting):
        self.meetings.append(meeting)

    def calculate_schedule(self):
        schedule = []
        current_time = datetime.strptime('09:00', '%H:%M')
        for meeting in self.meetings:
            travel_time = self.travel_times['Bayview'][meeting.location]
            if current_time + timedelta(minutes=travel_time) > datetime.strptime(meeting.start_time, '%H:%M'):
                current_time = datetime.strptime(meeting.start_time, '%H:%M')
            schedule.append({
                'action':'meet',
                'location': meeting.location,
                'person': meeting.person,
               'start_time': current_time.strftime('%H:%M'),
                'end_time': (current_time + timedelta(minutes=meeting.duration())).strftime('%H:%M')
            })
            current_time = datetime.strptime((current_time + timedelta(minutes=meeting.duration() + travel_time)).strftime('%H:%M'), '%H:%M')
        return schedule

def main():
    schedule = Schedule()
    meetings = [
        Meeting('Brian', 'North Beach', '13:00', '19:00'),
        Meeting('Richard', 'Fisherman\'s Wharf', '11:00', '12:45'),
        Meeting('Ashley', 'Haight-Ashbury', '15:00', '20:30'),
        Meeting('Elizabeth', 'Nob Hill', '11:45', '16:30'),
        Meeting('Jessica', 'Golden Gate Park', '20:00', '21:45'),
        Meeting('Deborah', 'Union Square', '17:30', '20:00'),
        Meeting('Kimberly', 'Alamo Square', '17:30', '20:15'),
        Meeting('Matthew', 'Presidio', '08:15', '09:00'),
        Meeting('Kenneth', 'Chinatown', '14:45', '20:30'),
        Meeting('Anthony', 'Pacific Heights', '14:15', '16:00')
    ]
    for meeting in meetings:
        schedule.add_meeting(meeting)
    schedule.calculate_schedule()
    print(json.dumps({'itinerary': schedule.calculate_schedule()}, indent=4))

if __name__ == "__main__":
    main()