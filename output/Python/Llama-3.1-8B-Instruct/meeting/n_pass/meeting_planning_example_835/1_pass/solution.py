import json
from datetime import datetime, timedelta

class MeetingPlanner:
    def __init__(self):
        self.travel_times = {
            'Pacific Heights': {
                'Golden Gate Park': 15,
                'The Castro': 16,
                'Bayview': 22,
                'Marina District': 6,
                'Union Square': 12,
                'Sunset District': 21,
                'Alamo Square': 10,
                'Financial District': 13,
                'Mission District': 15
            },
            'Golden Gate Park': {
                'Pacific Heights': 16,
                'The Castro': 13,
                'Bayview': 23,
                'Marina District': 16,
                'Union Square': 22,
                'Sunset District': 10,
                'Alamo Square': 9,
                'Financial District': 26,
                'Mission District': 17
            },
            'The Castro': {
                'Pacific Heights': 16,
                'Golden Gate Park': 11,
                'Bayview': 19,
                'Marina District': 21,
                'Union Square': 19,
                'Sunset District': 17,
                'Alamo Square': 8,
                'Financial District': 21,
                'Mission District': 7
            },
            'Bayview': {
                'Pacific Heights': 23,
                'Golden Gate Park': 22,
                'The Castro': 19,
                'Marina District': 27,
                'Union Square': 18,
                'Sunset District': 23,
                'Alamo Square': 16,
                'Financial District': 19,
                'Mission District': 13
            },
            'Marina District': {
                'Pacific Heights': 7,
                'Golden Gate Park': 18,
                'The Castro': 22,
                'Bayview': 27,
                'Union Square': 16,
                'Sunset District': 19,
                'Alamo Square': 15,
                'Financial District': 17,
                'Mission District': 20
            },
            'Union Square': {
                'Pacific Heights': 12,
                'Golden Gate Park': 22,
                'The Castro': 17,
                'Bayview': 15,
                'Marina District': 18,
                'Sunset District': 27,
                'Alamo Square': 15,
                'Financial District': 9,
                'Mission District': 14
            },
            'Sunset District': {
                'Pacific Heights': 21,
                'Golden Gate Park': 11,
                'The Castro': 17,
                'Bayview': 22,
                'Marina District': 21,
                'Union Square': 30,
                'Alamo Square': 17,
                'Financial District': 30,
                'Mission District': 25
            },
            'Alamo Square': {
                'Pacific Heights': 10,
                'Golden Gate Park': 9,
                'The Castro': 8,
                'Bayview': 16,
                'Marina District': 15,
                'Union Square': 14,
                'Sunset District': 16,
                'Financial District': 17,
                'Mission District': 10
            },
            'Financial District': {
                'Pacific Heights': 13,
                'Golden Gate Park': 23,
                'The Castro': 20,
                'Bayview': 19,
                'Marina District': 15,
                'Union Square': 9,
                'Sunset District': 30,
                'Alamo Square': 17,
                'Mission District': 17
            },
            'Mission District': {
                'Pacific Heights': 15,
                'Golden Gate Park': 17,
                'The Castro': 7,
                'Bayview': 14,
                'Marina District': 19,
                'Union Square': 15,
                'Sunset District': 24,
                'Alamo Square': 11,
                'Financial District': 15
            }
        }

        self.meeting_constraints = {
            'Helen': {'start_time': '09:30', 'end_time': '12:15','min_meeting_time': 45},
            'Steven': {'start_time': '20:15', 'end_time': '22:00','min_meeting_time': 105},
            'Deborah': {'start_time': '08:30', 'end_time': '12:00','min_meeting_time': 30},
            'Matthew': {'start_time': '09:15', 'end_time': '14:15','min_meeting_time': 45},
            'Joseph': {'start_time': '14:15', 'end_time': '18:45','min_meeting_time': 120},
            'Ronald': {'start_time': '16:00', 'end_time': '20:45','min_meeting_time': 60},
            'Robert': {'start_time': '18:30', 'end_time': '21:15','min_meeting_time': 120},
            'Rebecca': {'start_time': '14:45', 'end_time': '15:15','min_meeting_time': 30},
            'Elizabeth': {'start_time': '18:30', 'end_time': '21:00','min_meeting_time': 120}
        }

        self.start_time = '09:00'
        self.end_time = '23:59'

    def compute_meeting_schedule(self):
        # Sort the meeting constraints by start time
        sorted_constraints = sorted(self.meeting_constraints.items(), key=lambda x: x[1]['start_time'])

        # Initialize the schedule
        schedule = []

        # Initialize the current time
        current_time = datetime.strptime(self.start_time, '%H:%M')

        # Iterate over the meeting constraints
        for person, constraint in sorted_constraints:
            # Check if the person is available at the current time
            if current_time >= datetime.strptime(constraint['start_time'], '%H:%M') and current_time <= datetime.strptime(constraint['end_time'], '%H:%M'):
                # Calculate the travel time to the person's location
                travel_time = self.travel_times['Pacific Heights'][person]
                arrival_time = current_time + timedelta(minutes=travel_time)

                # Check if the arrival time is within the person's availability
                if arrival_time >= datetime.strptime(constraint['start_time'], '%H:%M') and arrival_time <= datetime.strptime(constraint['end_time'], '%H:%M'):
                    # Calculate the meeting time
                    meeting_time = max(constraint['min_meeting_time'], (arrival_time - current_time).total_seconds() / 60)

                    # Add the meeting to the schedule
                    schedule.append({
                        'action':'meet',
                        'location': person,
                        'person': person,
                       'start_time': current_time.strftime('%H:%M'),
                        'end_time': (current_time + timedelta(minutes=meeting_time)).strftime('%H:%M')
                    })

                    # Update the current time
                    current_time += timedelta(minutes=meeting_time)

        return schedule

    def print_schedule(self, schedule):
        print('SOLUTION:')
        for meeting in schedule:
            print(f"  {{ 'action': '{meeting['action']}', 'location': '{meeting['location']}', 'person': '{meeting['person']}','start_time': '{meeting['start_time']}', 'end_time': '{meeting['end_time']}' }}")

    def output_schedule(self, schedule):
        print(json.dumps({'itinerary': schedule}, indent=4))


if __name__ == '__main__':
    planner = MeetingPlanner()
    schedule = planner.compute_meeting_schedule()
    planner.output_schedule(schedule)