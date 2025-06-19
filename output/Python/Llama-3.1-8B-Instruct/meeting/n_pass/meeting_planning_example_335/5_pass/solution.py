import json
from datetime import datetime, timedelta

class MeetingPlanner:
    def __init__(self):
        self.travel_distances = {
            'Pacific Heights': {
                'North Beach': 9,
                'Financial District': 13,
                'Alamo Square': 10,
                'Mission District': 15
            },
            'North Beach': {
                'Pacific Heights': 8,
                'Financial District': 8,
                'Alamo Square': 16,
                'Mission District': 18
            },
            'Financial District': {
                'Pacific Heights': 13,
                'North Beach': 7,
                'Alamo Square': 17,
                'Mission District': 17
            },
            'Alamo Square': {
                'Pacific Heights': 10,
                'North Beach': 15,
                'Financial District': 17,
                'Mission District': 11
            },
            'Mission District': {
                'Pacific Heights': 16,
                'North Beach': 17,
                'Financial District': 17,
                'Alamo Square': 11
            }
        }

        self.constraints = {
            'Helen': {'location': 'North Beach','start_time': '09:00', 'end_time': '17:00', 'duration': 15},
            'Betty': {'location': 'Financial District','start_time': '19:00', 'end_time': '21:45', 'duration': 90},
            'Amanda': {'location': 'Alamo Square','start_time': '19:45', 'end_time': '21:00', 'duration': 60},
            'Kevin': {'location': 'Mission District','start_time': '10:45', 'end_time': '14:45', 'duration': 45}
        }

    def calculate_travel_time(self, start_location, end_location):
        return self.travel_distances.get(start_location, {}).get(end_location, 0)

    def check_constraint(self, person, start_time, end_time, duration):
        person_constraint = self.constraints[person]
        if start_time >= datetime.strptime(person_constraint['start_time'], '%H:%M') and end_time + timedelta(minutes=duration) <= datetime.strptime(person_constraint['end_time'], '%H:%M'):
            return True
        return False

    def find_optimal_schedule(self):
        optimal_schedule = []
        start_time = '10:45'  # Schedule meetings starting from Kevin's availability

        # Meet Kevin
        kevin_start_time = datetime.strptime(start_time, '%H:%M')
        kevin_end_time = kevin_start_time + timedelta(minutes=self.calculate_travel_time('Pacific Heights', 'Mission District'))
        kevin_end_time += timedelta(minutes=self.constraints['Kevin']['duration'])
        if kevin_end_time <= datetime.strptime(self.constraints['Kevin']['end_time'], '%H:%M'):
            optimal_schedule.append({
                'action':'meet',
                'location': 'Mission District',
                'person': 'Kevin',
           'start_time': start_time,
                'end_time': kevin_end_time.strftime('%H:%M')
            })
            start_time = kevin_end_time.strftime('%H:%M')

        # Meet Helen
        helen_start_time = datetime.strptime(start_time, '%H:%M')
        helen_end_time = helen_start_time + timedelta(minutes=self.calculate_travel_time('Mission District', 'North Beach'))
        helen_end_time += timedelta(minutes=self.constraints['Helen']['duration'])
        if helen_end_time <= datetime.strptime(self.constraints['Helen']['end_time'], '%H:%M'):
            optimal_schedule.append({
                'action':'meet',
                'location': 'North Beach',
                'person': 'Helen',
           'start_time': start_time,
                'end_time': helen_end_time.strftime('%H:%M')
            })
            start_time = helen_end_time.strftime('%H:%M')

        # Travel to Financial District
        start_time = (datetime.strptime(start_time, '%H:%M') + timedelta(minutes=self.calculate_travel_time('North Beach', 'Financial District'))).strftime('%H:%M')

        # Meet Amanda
        amanda_start_time = datetime.strptime(start_time, '%H:%M')
        amanda_end_time = amanda_start_time + timedelta(minutes=self.calculate_travel_time('Financial District', 'Alamo Square'))
        amanda_end_time += timedelta(minutes=self.constraints['Amanda']['duration'])
        if amanda_end_time <= datetime.strptime(self.constraints['Amanda']['end_time'], '%H:%M'):
            optimal_schedule.append({
                'action':'meet',
                'location': 'Alamo Square',
                'person': 'Amanda',
           'start_time': start_time,
                'end_time': amanda_end_time.strftime('%H:%M')
            })
            start_time = amanda_end_time.strftime('%H:%M')

        # Meet Betty
        betty_start_time = datetime.strptime(start_time, '%H:%M')
        betty_end_time = betty_start_time + timedelta(minutes=self.calculate_travel_time('Alamo Square', 'Financial District'))
        betty_end_time += timedelta(minutes=self.constraints['Betty']['duration'])
        if betty_end_time <= datetime.strptime(self.constraints['Betty']['start_time'], '%H:%M') + timedelta(minutes=self.constraints['Betty']['duration']):
            optimal_schedule.append({
                'action':'meet',
                'location': 'Financial District',
                'person': 'Betty',
           'start_time': start_time,
                'end_time': betty_end_time.strftime('%H:%M')
            })
            start_time = betty_end_time.strftime('%H:%M')

        return optimal_schedule

def main():
    planner = MeetingPlanner()
    optimal_schedule = planner.find_optimal_schedule()
    print(json.dumps({'itinerary': optimal_schedule}, indent=4))

if __name__ == "__main__":
    main()