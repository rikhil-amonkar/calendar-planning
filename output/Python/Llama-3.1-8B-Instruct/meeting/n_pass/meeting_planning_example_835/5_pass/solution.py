import json
from datetime import datetime, timedelta

class MeetingPlanner:
    def __init__(self):
        self.travel_times = {
            'Pacific Heights': {
                'Helen': 15,
                'Steven': 16,
                'Deborah': 10,
                'Matthew': 20,
                'Joseph': 25,
                'Ronald': 30,
                'Robert': 35,
                'Rebecca': 40,
                'Elizabeth': 45
            },
            'Golden Gate Park': {
                'Helen': 16,
                'Steven': 13,
                'Deborah': 11,
                'Matthew': 18,
                'Joseph': 23,
                'Ronald': 28,
                'Robert': 33,
                'Rebecca': 38,
                'Elizabeth': 43
            },
            'The Castro': {
                'Helen': 17,
                'Steven': 14,
                'Deborah': 12,
                'Matthew': 19,
                'Joseph': 24,
                'Ronald': 29,
                'Robert': 34,
                'Rebecca': 39,
                'Elizabeth': 44
            },
            'Bayview': {
                'Helen': 23,
                'Steven': 20,
                'Deborah': 18,
                'Matthew': 25,
                'Joseph': 30,
                'Ronald': 35,
                'Robert': 40,
                'Rebecca': 45,
                'Elizabeth': 50
            },
            'Marina District': {
                'Helen': 21,
                'Steven': 22,
                'Deborah': 19,
                'Matthew': 26,
                'Joseph': 31,
                'Ronald': 36,
                'Robert': 41,
                'Rebecca': 46,
                'Elizabeth': 51
            },
            'Union Square': {
                'Helen': 22,
                'Steven': 23,
                'Deborah': 20,
                'Matthew': 27,
                'Joseph': 32,
                'Ronald': 37,
                'Robert': 42,
                'Rebecca': 47,
                'Elizabeth': 52
            },
            'Sunset District': {
                'Helen': 24,
                'Steven': 25,
                'Deborah': 22,
                'Matthew': 29,
                'Joseph': 34,
                'Ronald': 39,
                'Robert': 44,
                'Rebecca': 49,
                'Elizabeth': 54
            },
            'Alamo Square': {
                'Helen': 25,
                'Steven': 26,
                'Deborah': 23,
                'Matthew': 30,
                'Joseph': 35,
                'Ronald': 40,
                'Robert': 45,
                'Rebecca': 50,
                'Elizabeth': 55
            },
            'Financial District': {
                'Helen': 26,
                'Steven': 27,
                'Deborah': 24,
                'Matthew': 31,
                'Joseph': 36,
                'Ronald': 41,
                'Robert': 46,
                'Rebecca': 51,
                'Elizabeth': 56
            },
            'Mission District': {
                'Helen': 27,
                'Steven': 28,
                'Deborah': 25,
                'Matthew': 32,
                'Joseph': 37,
                'Ronald': 42,
                'Robert': 47,
                'Rebecca': 52,
                'Elizabeth': 57
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
                # Get the person's location
                location = self.get_location(person)

                # Check if the location exists
                if location:
                    # Calculate the travel time to the person's location
                    travel_time = self.travel_times[location][person]

                    # Calculate the arrival time
                    arrival_time = current_time + timedelta(minutes=travel_time)

                    # Check if the arrival time is within the person's availability
                    if arrival_time >= datetime.strptime(constraint['start_time'], '%H:%M') and arrival_time <= datetime.strptime(constraint['end_time'], '%H:%M'):
                        # Check if the arrival time is not the same as the current time
                        if arrival_time!= current_time:
                            # Calculate the meeting time
                            meeting_time = max(constraint['min_meeting_time'], (arrival_time - current_time).total_seconds() / 60)

                            # Add the meeting to the schedule
                            schedule.append({
                                'action':'meet',
                                'location': location,
                                'person': person,
                               'start_time': current_time.strftime('%H:%M'),
                                'end_time': (current_time + timedelta(minutes=meeting_time)).strftime('%H:%M')
                            })

                            # Update the current time
                            current_time += timedelta(minutes=meeting_time)
                        else:
                            # If the arrival time is the same as the current time, add the meeting to the schedule
                            schedule.append({
                                'action':'meet',
                                'location': location,
                                'person': person,
                               'start_time': current_time.strftime('%H:%M'),
                                'end_time': (current_time + timedelta(minutes=constraint['min_meeting_time'])).strftime('%H:%M')
                            })

                            # Update the current time
                            current_time += timedelta(minutes=constraint['min_meeting_time'])
                else:
                    # If the person's location is not found, skip this person and continue with the next one
                    continue

        return schedule

    def get_location(self, person):
        # This function is used to get the location of a person
        # It assumes that the person's location is the same as the location in the travel_times dictionary
        # If the person is not found in the travel_times dictionary, it returns None
        for location, people in self.travel_times.items():
            if person in people:
                return location

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