import json
from datetime import datetime, timedelta

class SchedulePlanner:
    def __init__(self):
        self.travel_times = {
            ('Bayview', 'Nob Hill'): 20,
            ('Bayview', 'Union Square'): 17,
            ('Bayview', 'Chinatown'): 18,
            ('Bayview', 'The Castro'): 20,
            ('Bayview', 'Presidio'): 31,
            ('Bayview', 'Pacific Heights'): 23,
            ('Bayview', 'Russian Hill'): 23,
            ('Nob Hill', 'Union Square'): 7,
            ('Nob Hill', 'Chinatown'): 6,
            ('Nob Hill', 'The Castro'): 17,
            ('Nob Hill', 'Presidio'): 17,
            ('Nob Hill', 'Pacific Heights'): 8,
            ('Nob Hill', 'Russian Hill'): 5,
            ('Union Square', 'Chinatown'): 7,
            ('Union Square', 'The Castro'): 19,
            ('Union Square', 'Presidio'): 24,
            ('Union Square', 'Pacific Heights'): 15,
            ('Union Square', 'Russian Hill'): 13,
            ('Chinatown', 'The Castro'): 20,
            ('Chinatown', 'Presidio'): 19,
            ('Chinatown', 'Pacific Heights'): 10,
            ('Chinatown', 'Russian Hill'): 7,
            ('The Castro', 'Presidio'): 20,
            ('The Castro', 'Pacific Heights'): 16,
            ('The Castro', 'Russian Hill'): 18,
            ('Presidio', 'Pacific Heights'): 11,
            ('Presidio', 'Russian Hill'): 14,
            ('Pacific Heights', 'Russian Hill'): 7,
        }

        # Meeting constraints (start_time, end_time, minimum_meeting_time)
        self.meetings = {
            'Paul': ('16:15', '21:15', 60),
            'Carol': ('18:00', '20:15', 120),
            'Patricia': ('20:00', '21:30', 75),
            'Karen': ('17:00', '19:00', 45),
            'Nancy': ('11:45', '22:00', 30),
            'Jeffrey': ('20:00', '20:45', 45),
            'Matthew': ('15:45', '21:45', 75),
        }

        self.start_location = 'Bayview'
        self.start_time = datetime.strptime('09:00', '%H:%M')

        self.schedule = []

    def convert_to_minutes(self, time_str):
        time_obj = datetime.strptime(time_str, '%H:%M')
        return time_obj.hour * 60 + time_obj.minute

    def convert_to_time_str(self, total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours}:{minutes:02d}"

    def plan_schedule(self):
        available_meetings = {
            person: (self.convert_to_minutes(start), 
                      self.convert_to_minutes(end), 
                      min_time)
            for person, (start, end, min_time) in self.meetings.items()
        }

        current_time = self.start_time
        current_location = self.start_location

        # Visit Nancy first since it has the longest availability
        nancy_start, nancy_end, nancy_minutes = available_meetings['Nancy']
        travel_time_to_nancy = self.travel_times[(current_location, 'Presidio')]
        nancy_meeting_time = max(current_time + timedelta(minutes=travel_time_to_nancy), 
                                  datetime.strptime('11:45', '%H:%M'))

        # If we arrive after Nancy's meeting, skip to next
        if nancy_meeting_time < datetime.strptime('11:45', '%H:%M'):
            nancy_meeting_time = datetime.strptime('11:45', '%H:%M')

        self.schedule.append({
            'action': 'meet',
            'location': 'Presidio',
            'person': 'Nancy',
            'start_time': nancy_meeting_time.strftime('%H:%M'),
            'end_time': (nancy_meeting_time + timedelta(minutes=nancy_minutes)).strftime('%H:%M')
        })

        # Update current time and location
        current_time = nancy_meeting_time + timedelta(minutes=nancy_minutes)
        current_location = 'Presidio'

        # Meeting sequence based on available time
        for person in ['Matthew', 'Paul', 'Karen', 'Carol', 'Jeffrey', 'Patricia']:
            start, end, min_time = available_meetings[person]
            end_time = datetime.strptime(end, '%H:%M')

            while current_time.hour * 60 + current_time.minute < end:
                travel_time = self.travel_times.get((current_location, 'Nob Hill' if person == 'Paul' else 
                                                     'Union Square' if person == 'Carol' else 
                                                     'Chinatown' if person == 'Patricia' else
                                                     'The Castro' if person == 'Karen' else 
                                                     'Pacific Heights' if person == 'Jeffrey' else 
                                                     'Russian Hill' if person == 'Matthew' else 'Bayview'), float('inf'))

                meeting_start = current_time + timedelta(minutes=travel_time)
                if meeting_start.hour * 60 + meeting_start.minute <= end and (meeting_start + timedelta(minutes=min_time)).hour * 60 + (meeting_start + timedelta(minutes=min_time)).minute <= end:
                    self.schedule.append({
                        'action': 'meet',
                        'location': ('Nob Hill' if person == 'Paul' else
                                     'Union Square' if person == 'Carol' else 
                                     'Chinatown' if person == 'Patricia' else 
                                     'The Castro' if person == 'Karen' else 
                                     'Pacific Heights' if person == 'Jeffrey' else 
                                     'Russian Hill' if person == 'Matthew' else 'Bayview'),
                        'person': person,
                        'start_time': meeting_start.strftime('%H:%M'),
                        'end_time': (meeting_start + timedelta(minutes=min_time)).strftime('%H:%M')
                    })

                    # Update current time and location
                    current_time = meeting_start + timedelta(minutes=min_time)
                    current_location = ('Nob Hill' if person == 'Paul' else
                                        'Union Square' if person == 'Carol' else
                                        'Chinatown' if person == 'Patricia' else
                                        'The Castro' if person == 'Karen' else
                                        'Pacific Heights' if person == 'Jeffrey' else
                                        'Russian Hill' if person == 'Matthew' else 'Bayview')
                    if current_time.hour * 60 + current_time.minute >= 21 * 60:  # 21:00
                        break
                else:
                    break

        return self.schedule

if __name__ == "__main__":
    planner = SchedulePlanner()
    optimal_schedule = planner.plan_schedule()

    result = {
        "itinerary": optimal_schedule
    }

    print(json.dumps(result, indent=2))